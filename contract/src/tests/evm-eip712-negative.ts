// Test-only helpers for the `evm_eip712` constraint-level negatives (spec
// FR-019), on top of constraint-negative.ts:
//
//   - loadPatched: a copy of the compiled account module whose named asserts
//     record instead of throwing (as loadBypassedContract) AND whose named
//     runtime functions are replaced, so that a degenerate point can reach the
//     transcript; the patch is client-side only, the proof server still sees
//     the real constraints;
//   - a local account: a constructor state, then each call executed locally
//     from the previous call's state (the "simulator"), optionally proved by
//     the proof server; no node, no wallet.

import * as path from 'node:path';
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { randomUUID } from 'node:crypto';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import {
  createUnprovenCallTxFromInitialStates,
  createUnprovenDeployTxFromVerifierKeys,
} from '@midnight-ntwrk/midnight-js-contracts';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { LedgerParameters, ZswapChainState, sampleSigningKey } from '@midnightntwrk/ledger-v9';
// midnight-js keeps contract state in the on-chain runtime's classes (via compact-runtime).
import { ChargedState, ContractState } from '@midnight-ntwrk/compact-runtime';
import { CONFIG, zkConfigPath } from '../node/wallet.js';
import { emptyCoinStore, makeWitnesses } from '../wallet/witnesses.js';
import { recordingProofProvider, type BypassedContractModule, type ProofServerRequest } from './constraint-negative.js';

export const ACCOUNT_JS = path.join(zkConfigPath, 'contract', 'index.js');
export const Original: any = await import(pathToFileURL(ACCOUNT_JS).href);
export const zk = new NodeZkConfigProvider(zkConfigPath);
export const proofLog: ProofServerRequest[] = [];
export const proofProvider = recordingProofProvider(CONFIG.proofServer, zk, proofLog);
const coinPublicKey = '00'.repeat(32);
const encryptionPublicKey = '00'.repeat(32);
const privateState = emptyCoinStore(new Uint8Array(32).fill(7));

// ── Patched modules ─────────────────────────────────────────────────────────

const RUNTIME_IMPORT = "import * as __compactRuntime from '@midnight-ntwrk/compact-runtime';";
const REGISTRY = Symbol.for('midnight-passport.evm-eip712-negative');
const registry: Map<string, { messages: Set<string>; fired: Map<string, number> }> = ((globalThis as any)[REGISTRY] ??= new Map());

/** Lets the point at infinity, in either encoding, reach the transcript: the
 *  validator accepts (0, 0), and the coordinate accessors return 0 for the
 *  flagged identity instead of throwing. */
export const POINT_AT_INFINITY_OVERRIDES = `
  isValidSecp256k1Point(p) {
    if (p && p.x === 0n && p.y === 0n && typeof p.identity === 'boolean') return true;
    return __compactRuntimeOriginal.isValidSecp256k1Point(p);
  },
  secp256k1PointX(p) { return p && p.identity && p.x === 0n && p.y === 0n ? 0n : __compactRuntimeOriginal.secp256k1PointX(p); },
  secp256k1PointY(p) { return p && p.identity && p.x === 0n && p.y === 0n ? 0n : __compactRuntimeOriginal.secp256k1PointY(p); },`;

/** QA-1: lets a non-identity point whose coordinates are NOT reduced below the
 *  base-field modulus p (x + p, y + p) pass the validator AND reach the
 *  transcript as unreduced limbs: Secp256k1Base travels as (value - 1) in a
 *  low-192 / high-64 limb pair, and the honest encoder refuses value > p - 1;
 *  this one encodes value - 1 as given, the representation an honest encoder
 *  never produces. */
export const NON_CANONICAL_COORDINATE_OVERRIDES = `
  isValidSecp256k1Point(p) {
    const P = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn;
    if (p && !p.identity && typeof p.x === 'bigint' && typeof p.y === 'bigint' && (p.x >= P || p.y >= P) && p.x < (1n << 256n) && p.y < (1n << 256n)) {
      return __compactRuntimeOriginal.isValidSecp256k1Point({ x: p.x % P, y: p.y % P, identity: false });
    }
    return __compactRuntimeOriginal.isValidSecp256k1Point(p);
  },
  CompactTypeSecp256k1Point: {
    alignment: () => __compactRuntimeOriginal.CompactTypeSecp256k1Point.alignment(),
    fromValue: (v) => __compactRuntimeOriginal.CompactTypeSecp256k1Point.fromValue(v),
    toValue(v) {
      const P = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn;
      if (v.identity || (v.x < P && v.y < P)) return __compactRuntimeOriginal.CompactTypeSecp256k1Point.toValue(v);
      const limbs = (c) => { const r = c === 0n ? P - 1n : c - 1n; return __compactRuntimeOriginal.bigIntToValue(r & ((1n << 192n) - 1n)).concat(__compactRuntimeOriginal.bigIntToValue(r >> 192n)); };
      return limbs(v.x).concat(limbs(v.y)).concat(__compactRuntimeOriginal.bigIntToValue(0n));
    },
  },`;

export async function loadPatched(bypass: readonly string[], overrides = ''): Promise<BypassedContractModule> {
  const source = await readFile(ACCOUNT_JS, 'utf8');
  if (source.split(RUNTIME_IMPORT).length !== 2) throw new Error('evm-eip712-negative: unexpected runtime import');
  for (const m of bypass) {
    if (!source.includes(`'${m}'`) && !source.includes(JSON.stringify(m))) throw new Error(`evm-eip712-negative: no assert message ${JSON.stringify(m)}`);
  }
  const id = randomUUID();
  const state = { messages: new Set(bypass), fired: new Map<string, number>() };
  registry.set(id, state);
  const runtimeUrl = import.meta.resolve('@midnight-ntwrk/compact-runtime');
  const prelude = [
    `import * as __compactRuntimeOriginal from ${JSON.stringify(runtimeUrl)};`,
    `const __bypass = globalThis[Symbol.for('midnight-passport.evm-eip712-negative')].get(${JSON.stringify(id)});`,
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
  const dir = await mkdtemp(path.join(tmpdir(), 'evm-eip712-negative-'));
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

// ── A local account ─────────────────────────────────────────────────────────

const compiled = (C: any) => (CompiledContract.make('account', C) as any).pipe(
  (CompiledContract as any).withWitnesses(makeWitnesses()),
  (CompiledContract as any).withCompiledFileAssets(zkConfigPath),
);

export interface LocalAccount {
  contractAddress: string;
  addressBytes: Uint8Array;
  state: ContractState;
}

/** A dormant account: the constructor state with boot commitment `boot`. */
export async function dormant(boot: Uint8Array, recoveryPk: unknown): Promise<LocalAccount> {
  const deploy: any = await createUnprovenDeployTxFromVerifierKeys(zk as any, coinPublicKey, {
    compiledContract: compiled(Original.Contract), signingKey: sampleSigningKey(), initialPrivateState: privateState,
    args: [boot, new Uint8Array(32).fill(9), recoveryPk, new Uint8Array(64), 3n * 24n * 3600n],
  } as any, encryptionPublicKey);
  const contractAddress = String(deploy.public.contractAddress);
  return { contractAddress, addressBytes: new Uint8Array(Buffer.from(contractAddress, 'hex')), state: deploy.public.initialContractState };
}

/** The decoded ledger of a local account. */
export const ledgerOf = (a: LocalAccount): any => Original.ledger(a.state.data);

/** Executes `circuitId` locally with module `C` against `a`'s state (the
 *  generated JavaScript is the simulator: a failed assert throws here). */
export async function execute(C: any, a: LocalAccount, circuitId: string, args: unknown[]) {
  const call: any = await createUnprovenCallTxFromInitialStates(zk as any, {
    compiledContract: compiled(C), circuitId, contractAddress: a.contractAddress, coinPublicKey,
    initialContractState: a.state, initialZswapChainState: new ZswapChainState(),
    ledgerParameters: LedgerParameters.initialParameters(), args, initialPrivateState: privateState,
  } as any, encryptionPublicKey);
  const next = ContractState.deserialize(a.state.serialize());
  next.data = new ChargedState(call.public.nextContractState);
  return { call, after: { ...a, state: next } as LocalAccount };
}

/** Executes locally, then proves the call at the proof server. */
export async function prove(C: any, a: LocalAccount, circuitId: string, args: unknown[]) {
  const { call, after } = await execute(C, a, circuitId, args);
  const proven = await proofProvider.proveTx({ version: 'v9', tx: call.private.unprovenTx } as any);
  return { proven, after };
}
