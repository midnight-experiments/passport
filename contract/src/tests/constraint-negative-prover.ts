// Constraint-level negatives of the base modules, at the proof server.
//
// For every assert of the readable-descriptor and rendering modules, through
// the base probe contract's impure probe_* circuits:
//
//   positive   the honest call, built with the patched module (the same path
//              as the negatives), is proved by the proof server; it is
//              recorded as that module's positive control, and the prover
//              negative requires it (audit G1(E) F-A8);
//   runtime    the bad call, built with the original module, is refused by the
//              generated JavaScript (the usual first line of defence);
//   prover     the bad call, built with that one assert bypassed in the
//              generated JavaScript, reaches the proof server and is refused
//              there: the assert is a constraint of the proof.
//
// The calls are built from the probe's constructor state (no deploy, no node,
// no wallet) and only proved, never submitted. Needs a proof server at
// upstream's endpoint (CONFIG.proofServer, 127.0.0.1:6300); a missing proof
// server is an ERROR, never a pass. Writes
// $EVIDENCE_DIR/constraint-negative-prover.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import {
  createUnprovenCallTxFromInitialStates,
  createUnprovenDeployTxFromVerifierKeys,
} from '@midnight-ntwrk/midnight-js-contracts';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { LedgerParameters, ZswapChainState, sampleSigningKey } from '@midnightntwrk/ledger-v9';
import * as Original from '../../contracts/managed/probe-wallet-arms-base/contract/index.js';
import { CONFIG, managedPath } from '../node/wallet.js';
import {
  expectRefusal, expectSuccess, loadBypassedContract, recordingProofProvider,
  type NegativeResult, type PositiveResult, type ProofServerRequest,
} from './constraint-negative.js';

const PROBE = path.join(managedPath, 'probe-wallet-arms-base');
const PROBE_JS = path.join(PROBE, 'contract', 'index.js');
const zk = new NodeZkConfigProvider(PROBE);
const coinPublicKey = '00'.repeat(32);
const encryptionPublicKey = '00'.repeat(32);
const log: ProofServerRequest[] = [];
const proofProvider = recordingProofProvider(CONFIG.proofServer, zk, log);

const compiled = (C: any) => (CompiledContract.make('probe-wallet-arms-base', C) as any).pipe(
  (CompiledContract as any).withVacantWitnesses,
  (CompiledContract as any).withCompiledFileAssets(PROBE),
);
const deploy: any = await createUnprovenDeployTxFromVerifierKeys(zk as any, coinPublicKey, {
  compiledContract: compiled(Original.Contract), signingKey: sampleSigningKey(), initialPrivateState: {},
} as any, encryptionPublicKey);
const contractAddress = deploy.public.contractAddress;
const initialContractState = deploy.public.initialContractState;

/** Builds the call from the constructor state with module `C`, then proves it. */
const prove = async (C: any, circuitId: string, args: unknown[]) => {
  const call: any = await createUnprovenCallTxFromInitialStates(zk as any, {
    compiledContract: compiled(C), circuitId, contractAddress, coinPublicKey, initialContractState,
    initialZswapChainState: new ZswapChainState(), ledgerParameters: LedgerParameters.initialParameters(),
    args, initialPrivateState: {},
  } as any, encryptionPublicKey);
  return proofProvider.proveTx({ version: 'v9', tx: call.private.unprovenTx } as any);
};

const pad = (s: string, w = 32) => { const o = new Uint8Array(w); o.set(Buffer.from(s, 'latin1')); return o; };
const fill = (n: number, v: number) => new Uint8Array(n).fill(v);
const A = { bytes: fill(32, 0x11) };
const B32 = fill(32, 0x22), B20 = fill(20, 0x33), B21 = new Uint8Array(Buffer.from('https://a.example.com'));
const spaced = (s: string) => { const o = new Uint8Array(32).fill(0x20); o.set(Buffer.from(s, 'ascii')); return o; };
const digits = (s: string) => [...Buffer.from(s.padEnd(39, ' '), 'ascii')].map(BigInt);

// [circuit, honest arguments, bad arguments, the assert the bad call fails]
const CASES: [string, unknown[], unknown[], string][] = [
  ['probe_entry_w52', [pad('midnight:account:device:evm:v1'), A, B20, B32, 0n, 0n], [pad('midnight:account:device:sol:v1'), A, B20, B32, 0n, 0n], 'descriptor: not a 52-byte device tag'],
  ['probe_entry_w64', [pad('midnight:account:device:sol:v1'), A, B32, B32, 0n, 0n], [pad('midnight:account:device:k1:v2'), A, B32, B32, 0n, 0n], 'descriptor: not a 64-byte device tag'],
  ['probe_entry_w65', [pad('midnight:account:device:k1:v2'), A, B32, B32, 1n, 0n, 0n], [pad('midnight:account:device:ed:v1'), A, B32, B32, 1n, 0n, 0n], 'descriptor: not a 65-byte device tag'],
  ['probe_entry_w117', [pad('midnight:account:device:r1:v2'), A, B32, B32, B32, B21, 0n, 0n], [pad('midnight:account:grant:id:r1:v1'), A, B32, B32, B32, B21, 0n, 0n], 'descriptor: not a 117-byte device tag'],
  ['probe_boot_w52', [pad('midnight:account:boot:evm:v1'), B32, B20, B32], [pad('midnight:account:device:evm:v1'), B32, B20, B32], 'descriptor: not a 52-byte boot tag'],
  ['probe_boot_w64', [pad('midnight:account:boot:sol:v1'), B32, B32, B32], [pad('midnight:account:boot:k1:v2'), B32, B32, B32], 'descriptor: not a 64-byte boot tag'],
  ['probe_boot_w65', [pad('midnight:account:boot:k1:v2'), B32, B32, B32, 0n], [fill(32, 0x5a), B32, B32, B32, 0n], 'descriptor: not a 65-byte boot tag'],
  ['probe_boot_w117', [pad('midnight:account:boot:r1:v2'), B32, B32, B32, B32, B21], [pad('midnight:account:boot:v1'), B32, B32, B32, B32, B21], 'descriptor: not a 117-byte boot tag'],
  ['probe_grant_id_w52', [pad('midnight:account:grant:id:evm:v1'), A, B20, B32, B32, 0n], [pad('midnight:account:grant:id:sol:v1'), A, B20, B32, B32, 0n], 'descriptor: not a 52-byte grant-id tag'],
  ['probe_grant_id_w64', [pad('midnight:account:grant:id:r1:v1'), A, B32, B32, B32, 3n], [pad('midnight:account:grant:id:k1:v1'), A, B32, B32, B32, 3n], 'descriptor: not a 64-byte grant-id tag'],
  ['probe_grant_id_w65', [pad('midnight:account:grant:id:k1:v1'), A, B32, B32, 0n, B32, 3n], [pad('midnight:account:device:k1:v2'), A, B32, B32, 0n, B32, 3n], 'descriptor: not a 65-byte grant-id tag'],
  ['probe_blind', [pad('midnight:account:blind:sol:v1'), fill(64, 0x44)], [spaced('midnight:account:blind:evm:v1'), fill(64, 0x44)], 'descriptor: not a blind tag'],
  ['probe_uint128_text', [1000000n, digits('1000000')], [1000000n, digits('1000001')], 'display: digits do not match the value'],
  ['probe_uint128_text', [7n, digits('7')], [7n, digits('07')], 'display: leading zero'],
  ['probe_label_text_32', [pad('Midnight Night Market')], [pad('Midnight Night Market ')], 'display: not a zero-padded label'],
  ['probe_visible_text_21', [B21], [new Uint8Array(Buffer.from('https://a example.com'))], 'display: not visible ASCII'],
];

const results: { circuit: string; assert: string; positive: PositiveResult; runtime: NegativeResult; prover: NegativeResult }[] = [];
let failures = 0, errors = 0;
for (const [circuit, good, badArgs, message] of CASES) {
  const bypassed = await loadBypassedContract(PROBE_JS, [message]);
  const positive = await expectSuccess({ name: `${circuit}: honest call proved`, proofLog: log, through: bypassed, attempt: () => prove(bypassed.Contract, circuit, good) });
  const runtime = await expectRefusal({ name: `${circuit}: ${message} (generated JavaScript)`, expectedLayer: 'runtime', proofLog: log, attempt: () => prove(Original.Contract, circuit, badArgs) });
  const prover = await expectRefusal({ name: `${circuit}: ${message} (JavaScript check bypassed)`, expectedLayer: 'prover', bypassed, proofLog: log, requirePositiveControl: true, attempt: () => prove(bypassed.Contract, circuit, badArgs) });
  for (const r of [positive, runtime, prover]) { if (r.verdict === 'FAIL') failures++; if (r.verdict === 'ERROR') errors++; }
  results.push({ circuit, assert: message, positive: { ...positive, result: undefined }, runtime, prover });
  console.log(`  ${positive.verdict === 'PASS' && runtime.verdict === 'PASS' && prover.verdict === 'PASS' ? '✓' : '✗'} ${circuit} — "${message}": positive ${positive.verdict}, runtime ${runtime.verdict}, prover ${prover.verdict} (${prover.layer}${prover.proofServer.at(-1)?.status ? `, ${prover.proofServer.at(-1)!.endpoint} ${prover.proofServer.at(-1)!.status}` : ''})`);
  if (positive.verdict !== 'PASS') console.log(`      positive: ${positive.reason} ${positive.detail ?? ''}`);
  if (prover.verdict !== 'PASS') console.log(`      prover: ${prover.reason} ${prover.detail ?? ''}`);
}
const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'constraint-negative-prover.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify({
    suite: 'constraint-negative-prover', ranAt: new Date().toISOString(), proofServer: CONFIG.proofServer,
    contractAddress, cases: results, requests: log.length, verdict,
  }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ constraint-negative-prover: ${verdict} (${CASES.length} asserts; ${failures} FAIL, ${errors} ERROR; ${log.length} proof-server requests)`);
process.exit(verdict === 'PASS' ? 0 : 1);
