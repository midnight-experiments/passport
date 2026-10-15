// Constraint-level negatives of the `evm_eip712` arm, at the proof server
// (spec FR-019): the calls are built from a fresh account's constructor state
// (no deploy, no node, no wallet) and only proved, never submitted.
//
// For every case:
//   positive   the honest call, built with the PATCHED module (the same path
//              as the negatives), is proved by the proof server;
//   runtime    the bad call, built with the original module, is refused by the
//              generated JavaScript (or by the runtime's own type checks);
//   prover     the bad call, built with the named asserts bypassed (and, for a
//              degenerate point, the runtime's point validators relaxed so the
//              point reaches the transcript), is refused by the proof server:
//              the rule is a constraint of the proof.
//
// S2E cases (activate_initial_device_with_evm_eip712):
//   - a wrong blind for the committed address;
//   - another key's point (a wrong address) with the committed blind;
//   - the point at infinity, flagged {0, 0, identity}: the boot commitment is
//     made to match the address keccak256(0^64)[12..] it would hash to, so
//     only the identity guards stand between it and activation;
//   - the point at infinity, unflagged {0, 0, not identity} (off the curve),
//     likewise.
//
// Needs a proof server at upstream's endpoint (CONFIG.proofServer); a missing
// proof server is an ERROR, never a pass. Writes
// $EVIDENCE_DIR/evm-eip712-prover.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { randomUUID, createHash } from 'node:crypto';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import {
  createUnprovenCallTxFromInitialStates,
  createUnprovenDeployTxFromVerifierKeys,
} from '@midnight-ntwrk/midnight-js-contracts';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { LedgerParameters, ZswapChainState, sampleSigningKey } from '@midnightntwrk/ledger-v9';
import { CONFIG, zkConfigPath } from '../node/wallet.js';
import { emptyCoinStore, makeWitnesses } from '../wallet/witnesses.js';
import { JubjubDevice } from '../wallet/signer.js';
import { SoftwareEvmWallet, EvmEip712Device } from '../wallet/signer-evm-eip712.js';
import {
  expectRefusal, expectSuccess, recordingProofProvider,
  type BypassedContractModule, type NegativeResult, type PositiveResult, type ProofServerRequest,
} from './constraint-negative.js';

const ACCOUNT_JS = path.join(zkConfigPath, 'contract', 'index.js');
const Original = await import(pathToFileURL(ACCOUNT_JS).href);
const zk = new NodeZkConfigProvider(zkConfigPath);
const coinPublicKey = '00'.repeat(32);
const encryptionPublicKey = '00'.repeat(32);
const log: ProofServerRequest[] = [];
const proofProvider = recordingProofProvider(CONFIG.proofServer, zk, log);
const privateState = emptyCoinStore(new Uint8Array(32).fill(7));

// ── A patched module: named asserts bypassed, runtime functions replaced ────
//
// Like constraint-negative.ts's loadBypassedContract, plus OVERRIDES of named
// runtime functions (the patch is client-side only: it lets a bad call reach
// the transcript; the proof server still sees the real constraints).

const RUNTIME_IMPORT = "import * as __compactRuntime from '@midnight-ntwrk/compact-runtime';";
const REGISTRY = Symbol.for('midnight-passport.evm-eip712-prover');
const registry: Map<string, { messages: Set<string>; fired: Map<string, number> }> = ((globalThis as any)[REGISTRY] ??= new Map());

/** Runtime overrides that let the point at infinity, in either encoding, reach
 *  the transcript: the validator accepts (0, 0), and the coordinate accessors
 *  return 0 for the flagged identity instead of throwing. */
const POINT_AT_INFINITY_OVERRIDES = `
  isValidSecp256k1Point(p) {
    if (p && p.x === 0n && p.y === 0n && typeof p.identity === 'boolean') return true;
    return __compactRuntimeOriginal.isValidSecp256k1Point(p);
  },
  secp256k1PointX(p) { return p && p.identity && p.x === 0n && p.y === 0n ? 0n : __compactRuntimeOriginal.secp256k1PointX(p); },
  secp256k1PointY(p) { return p && p.identity && p.x === 0n && p.y === 0n ? 0n : __compactRuntimeOriginal.secp256k1PointY(p); },`;

async function loadPatched(bypass: readonly string[], overrides = ''): Promise<BypassedContractModule> {
  const source = await readFile(ACCOUNT_JS, 'utf8');
  if (source.split(RUNTIME_IMPORT).length !== 2) throw new Error('evm-eip712-prover: unexpected runtime import');
  for (const m of bypass) {
    if (!source.includes(`'${m}'`) && !source.includes(JSON.stringify(m))) throw new Error(`evm-eip712-prover: no assert message ${JSON.stringify(m)}`);
  }
  const id = randomUUID();
  const state = { messages: new Set(bypass), fired: new Map<string, number>() };
  registry.set(id, state);
  const runtimeUrl = import.meta.resolve('@midnight-ntwrk/compact-runtime');
  const prelude = [
    `import * as __compactRuntimeOriginal from ${JSON.stringify(runtimeUrl)};`,
    `const __bypass = globalThis[Symbol.for('midnight-passport.evm-eip712-prover')].get(${JSON.stringify(id)});`,
    'const __compactRuntime = Object.freeze({',
    '  ...__compactRuntimeOriginal,',
    overrides,
    '  assert(condition, message) {',
    '    if (!condition && __bypass.messages.has(message)) {',
    '      __bypass.fired.set(message, (__bypass.fired.get(message) ?? 0) + 1);',
    '      return;',
    '    }',
    '    return __compactRuntimeOriginal.assert(condition, message);',
    '  },',
    '});',
  ].join('\n');
  const dir = await mkdtemp(path.join(tmpdir(), 'evm-eip712-prover-'));
  const file = path.join(dir, 'index.mjs');
  await writeFile(file, source.replace(RUNTIME_IMPORT, prelude).replace(/^\/\/# sourceMappingURL=.*$/m, ''));
  const module = await import(pathToFileURL(file).href);
  return {
    module, Contract: module.Contract, ledger: module.ledger, pureCircuits: module.pureCircuits,
    bypassed: [...bypass],
    fired: () => [...state.fired].map(([message, count]) => ({ message, count })),
    resetFired: () => state.fired.clear(),
    file,
  };
}

// ── Calls from a fresh account's constructor state ──────────────────────────

const compiled = (C: any) => (CompiledContract.make('account', C) as any).pipe(
  (CompiledContract as any).withWitnesses(makeWitnesses()),
  (CompiledContract as any).withCompiledFileAssets(zkConfigPath),
);
const recoveryPk = JubjubDevice.generate().pk;

/** A dormant account (constructor state only) whose boot commitment is `boot`. */
async function dormant(boot: Uint8Array) {
  const deploy: any = await createUnprovenDeployTxFromVerifierKeys(zk as any, coinPublicKey, {
    compiledContract: compiled(Original.Contract), signingKey: sampleSigningKey(), initialPrivateState: privateState,
    args: [boot, new Uint8Array(32).fill(9), recoveryPk, new Uint8Array(64), 3n * 24n * 3600n],
  } as any, encryptionPublicKey);
  return { contractAddress: deploy.public.contractAddress, initialContractState: deploy.public.initialContractState };
}

/** Builds the call with module `C` from `account`'s state, then proves it. */
async function prove(C: any, account: { contractAddress: any; initialContractState: any }, circuitId: string, args: unknown[]) {
  const call: any = await createUnprovenCallTxFromInitialStates(zk as any, {
    compiledContract: compiled(C), circuitId, contractAddress: account.contractAddress, coinPublicKey,
    initialContractState: account.initialContractState, initialZswapChainState: new ZswapChainState(),
    ledgerParameters: LedgerParameters.initialParameters(), args, initialPrivateState: privateState,
  } as any, encryptionPublicKey);
  return proofProvider.proveTx({ version: 'v9', tx: call.private.unprovenTx } as any);
}

// ── Cases ────────────────────────────────────────────────────────────────────

const SEED = 'aa00067/e/s2/evm-eip712-prover/v1';
let ctr = 0;
const rnd = (n: number) => new Uint8Array(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, n));
const ACTIVATE = 'activate_initial_device_with_evm_eip712';
const INFINITY = 'evm_eip712: device key is the point at infinity';
const STDLIB_IDENTITY = 'Secp256k1Point identity is not a permitted input to secp256k1EthereumAddress';
const BOOT = 'boot commitment mismatch';

const wallet = new SoftwareEvmWallet(0xa11ce5n);
const device = await EvmEip712Device.enrol(wallet, 'undeployed', 0);
const other = new SoftwareEvmWallet(0xb0bn);
const salt = rnd(32);
const honestBoot = device.bootCommitment(salt);
// The "address" the point at infinity would hash to: keccak256(0^64)[12..].
const infinityAddress = keccak_256(new Uint8Array(64)).subarray(12);
const infinityBoot = (Original.pureCircuits as any).derive_boot_commitment_with_evm_eip712(salt, infinityAddress, device.blind);

interface Case { name: string; boot: Uint8Array; good: unknown[]; bad: unknown[]; bypass: string[]; overrides?: string; runtimeExpect: string }
const CASES: Case[] = [
  { name: 'wrong blind', boot: honestBoot, good: device.activationArgs(salt), bad: [device.pk, salt, rnd(32)], bypass: [BOOT], runtimeExpect: BOOT },
  { name: 'wrong address (another key, the committed blind)', boot: honestBoot, good: device.activationArgs(salt), bad: [other.pk, salt, device.blind], bypass: [BOOT], runtimeExpect: BOOT },
  { name: 'point at infinity, flagged {0, 0, identity}', boot: infinityBoot, good: device.activationArgs(salt), bad: [{ x: 0n, y: 0n, identity: true }, salt, device.blind],
    bypass: [INFINITY, STDLIB_IDENTITY], overrides: POINT_AT_INFINITY_OVERRIDES, runtimeExpect: 'identity point' },
  { name: 'point at infinity, unflagged {0, 0, not identity}', boot: infinityBoot, good: device.activationArgs(salt), bad: [{ x: 0n, y: 0n, identity: false }, salt, device.blind],
    bypass: [INFINITY], overrides: POINT_AT_INFINITY_OVERRIDES, runtimeExpect: 'expected value of type Secp256k1Point' },
];

const results: any[] = [];
let failures = 0, errors = 0;
for (const c of CASES) {
  const patched = await loadPatched(c.bypass, c.overrides ?? '');
  // The positive control uses the honest boot (its own dormant account), through the patched path.
  const positive: PositiveResult = await expectSuccess({ name: `${ACTIVATE}: honest activation proved (patched path)`, proofLog: log,
    attempt: async () => prove(patched.Contract, await dormant(honestBoot), ACTIVATE, c.good) });
  const acct = await dormant(c.boot);
  const runtime: NegativeResult = await expectRefusal({ name: `${ACTIVATE}: ${c.name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog: log,
    attempt: () => prove(Original.Contract, acct, ACTIVATE, c.bad) });
  const prover: NegativeResult = await expectRefusal({ name: `${ACTIVATE}: ${c.name} (JavaScript checks bypassed)`, expectedLayer: 'prover', bypassed: patched, proofLog: log,
    attempt: () => prove(patched.Contract, acct, ACTIVATE, c.bad) });
  const runtimeMessageOk = runtime.verdict === 'PASS' && String(runtime.detail ?? '').includes(c.runtimeExpect);
  if (runtime.verdict === 'PASS' && !runtimeMessageOk) { runtime.verdict = 'FAIL'; runtime.reason = `refused at runtime, but not by "${c.runtimeExpect}"`; }
  for (const r of [positive, runtime, prover]) { if (r.verdict === 'FAIL') failures++; if (r.verdict === 'ERROR') errors++; }
  results.push({ circuit: ACTIVATE, case: c.name, bypassed: c.bypass, runtimeOverrides: c.overrides ? 'point-at-infinity validators relaxed' : 'none',
    positive: { ...positive, result: undefined }, runtime, prover });
  const last = prover.proofServer.at(-1);
  console.log(`  ${positive.verdict === 'PASS' && runtime.verdict === 'PASS' && prover.verdict === 'PASS' ? '✓' : '✗'} ${c.name}: positive ${positive.verdict}, runtime ${runtime.verdict}, prover ${prover.verdict} (${prover.layer}${last?.status ? `, ${last.endpoint} ${last.status}` : ''})`);
  if (positive.verdict !== 'PASS') console.log(`      positive: ${positive.reason} ${positive.detail ?? ''}`);
  if (runtime.verdict !== 'PASS') console.log(`      runtime: ${runtime.reason} ${runtime.detail ?? ''}`);
  if (prover.verdict !== 'PASS') console.log(`      prover: ${prover.reason} ${prover.detail ?? ''}`);
}

const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'evm-eip712-prover.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify({ suite: 'evm-eip712-prover', step: 'S2E', ranAt: new Date().toISOString(), proofServer: CONFIG.proofServer,
    device: { address: device.checksumAddress }, cases: results, requests: log.length, verdict,
  }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ evm-eip712-prover: ${verdict} (${CASES.length} cases; ${failures} FAIL, ${errors} ERROR; ${log.length} proof-server requests)`);
process.exit(verdict === 'PASS' ? 0 : 1);
