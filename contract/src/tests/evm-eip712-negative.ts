// Test-only helpers for the `evm_eip712` constraint-level negatives (spec
// FR-019), on top of constraint-negative.ts:
//
//   - loadPatched: constraint-negative.ts's loadBypassedContract over the
//     compiled account module (named asserts record instead of throwing;
//     named runtime functions replaced through `overrides`, so that a
//     degenerate point can reach the transcript; a copy with overrides needs
//     a positive control proved through it); the patch is client-side only,
//     the proof server still sees the real constraints;
//   - a local account: a constructor state, then each call executed locally
//     from the previous call's state (the "simulator"), optionally proved by
//     the proof server; no node, no wallet;
//   - a local Zswap commitment tree holding chosen contract-owned coins at
//     known indexes, and a coin store whose `held_coin` answers are chosen
//     by the test (witness substitution, S6E): the Zswap half of a shielded
//     spend is then valid, so a refusal is the arm circuit's own;
//   - a malicious-prover mutant that forges the address the generated
//     JavaScript derives from the device's point (audit G1E-1), as a runtime
//     override of `keccak256`: the victim's entry matches while the attacker's
//     key signs, and only the proof's own derivation can refuse it.

import * as path from 'node:path';
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import {
  createUnprovenCallTxFromInitialStates,
  createUnprovenDeployTxFromVerifierKeys,
} from '@midnight-ntwrk/midnight-js-contracts';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { LedgerParameters, ZswapChainState, ZswapOffer, ZswapOutput, ZswapSecretKeys, sampleSigningKey } from '@midnightntwrk/ledger-v9';
// midnight-js keeps contract state in the on-chain runtime's classes (via compact-runtime).
import { ChargedState, ContractState } from '@midnight-ntwrk/compact-runtime';
import { CONFIG, zkConfigPath } from '../node/wallet.js';
import { emptyCoinStore, makeWitnesses, type CoinStorePrivateState } from '../wallet/witnesses.js';
import { loadBypassedContract, recordingProofProvider, type BypassedContractModule, type ProofServerRequest } from './constraint-negative.js';

export const ACCOUNT_JS = path.join(zkConfigPath, 'contract', 'index.js');
export const Original: any = await import(pathToFileURL(ACCOUNT_JS).href);
export const zk = new NodeZkConfigProvider(zkConfigPath);
export const proofLog: ProofServerRequest[] = [];

// Transport (diagnosed at S6E, evidence e/s6/logs/diag-epipe.log): the
// recording provider posts with fetch, whose pooled keep-alive connections
// the proof server (through the runner's forwarder) has sometimes closed by
// the time a prover key of several hundred MB is uploaded on them, and the
// upload then breaks with EPIPE before the proof server sees the request.
// The same proof over a fresh connection per request always went through.
// So this process's fetch dispatcher keeps no idle connection (keep-alive
// 1 ms): every request opens its own. Requests, answers and verdicts are
// unchanged; only connection reuse is.
{
  const KEY = Symbol.for('undici.globalDispatcher.1');
  try { await fetch(new URL('/health', CONFIG.proofServer), { signal: AbortSignal.timeout(5000) }); } catch { /* creates the dispatcher either way */ }
  const current: any = (globalThis as any)[KEY];
  if (current && !current.aa00067FreshConnections) {
    const fresh = new current.constructor({ keepAliveTimeout: 1, keepAliveMaxTimeout: 1 });
    fresh.aa00067FreshConnections = true;
    (globalThis as any)[KEY] = fresh;
  }
}
export const proofProvider = recordingProofProvider(CONFIG.proofServer, zk, proofLog);
const coinPublicKey = '00'.repeat(32);
const encryptionPublicKey = '00'.repeat(32);
const privateState = emptyCoinStore(new Uint8Array(32).fill(7));

// ── Patched modules ─────────────────────────────────────────────────────────


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

/** The forged-address mutant (audit G1E-1), as a runtime override: the
 *  generated JavaScript derives an address as keccak256 over the point's
 *  big-endian coordinates `[x_be, y_be]`; for the point `forgery.set` names,
 *  this override returns 12 bytes and then the chosen address, so the copy
 *  derives that address from the attacker's point. Any other hash is the
 *  real one, so honest calls through the copy behave as through the
 *  original (its positive control proves one). */
export const FORGE_ADDRESS_OVERRIDES = `
  keccak256(descriptor, value) {
    const f = globalThis[Symbol.for('aa00067.e.forgeAddress')];
    // the stdlib hashes [Vector<32, Uint<8>>, Vector<32, Uint<8>>] (arrays of
    // bigints); accept Bytes<32> (Uint8Array) as well
    const bytes = (b) => (b instanceof Uint8Array || Array.isArray(b)) && b.length === 32 ? Uint8Array.from(b, (v) => Number(v)) : null;
    if (f && Array.isArray(value) && value.length === 2 && bytes(value[0]) && bytes(value[1])) {
      const r = f(bytes(value[0]), bytes(value[1]));
      if (r) return r;
    }
    return __compactRuntimeOriginal.keccak256(descriptor, value);
  },`;

const FORGE = Symbol.for('aa00067.e.forgeAddress');
const be32 = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };

/** The target of FORGE_ADDRESS_OVERRIDES: the copy derives `address` from
 *  `pk`. Counts the forgeries (a mutant case is valid only if one fired). */
export const forgery = {
  set(target: { pk: { x: bigint; y: bigint }; address: Uint8Array } | undefined) {
    const x = target && be32(target.pk.x), y = target && be32(target.pk.y);
    (globalThis as any)[FORGE] = target && ((a: Uint8Array, b: Uint8Array) => {
      if (!a.every((v, i) => v === x![i]) || !b.every((v, i) => v === y![i])) return undefined;
      forgery.fired++;
      return new Uint8Array([...new Uint8Array(12).fill(0xee), ...target.address]);
    });
    forgery.fired = 0;
  },
  fired: 0,
};

/** A patched copy of the account module (constraint-negative.ts). */
export const loadPatched = (bypass: readonly string[], overrides = ''): Promise<BypassedContractModule> =>
  loadBypassedContract(ACCOUNT_JS, bypass, { overrides });

// ── A call builder for a direct transfer's first half ───────────────────────
//
// midnight-js 5.0.0-rc.2 refuses to assemble a call whose shielded output is
// addressed to a contract that does not claim it inside the SAME call tree
// (`assertReceivesMatchClaims`: "A shielded coin addressed to a contract must
// be claimed as received by that contract..."). A direct transfer
// (`withdraw_shielded_to_contract_*`, MIP-0012 §6.6) is claimed by the
// recipient's own `deposit_shielded` call in another intent of the same
// transaction, the composition upstream's custody-payments suite builds by
// grafting the recipient's intent onto the sender's call. So the sender's
// half can only be built with that client-side pre-check removed. This loads
// a copy of midnight-js-contracts whose only change is that call (its bare
// imports resolved to the same module instances); the node still checks the
// claim on the composed transaction, and proving does not depend on it.
const MJS_CHECK = '    assertReceivesMatchClaims(calls, segmentedOffers);\n';
let relaxed: any;
export async function relaxedContractsModule(): Promise<any> {
  if (relaxed) return relaxed;
  const url = import.meta.resolve('@midnight-ntwrk/midnight-js-contracts');
  const src = await readFile(new URL(url), 'utf8');
  if (src.split(MJS_CHECK).length !== 2) throw new Error('evm-eip712-negative: midnight-js claim pre-check not found where expected');
  let body = src.replace(MJS_CHECK, '    /* aa00067: claim pre-check removed for a grafted direct transfer */\n');
  body = body.replace(/from '(@[^']+)'/g, (_m, spec) => `from ${JSON.stringify(import.meta.resolve(spec))}`)
             .replace(/from 'effect'/g, `from ${JSON.stringify(import.meta.resolve('effect'))}`)
             .replace(/^\/\/# sourceMappingURL=.*$/m, '');
  const dir = await mkdtemp(path.join(tmpdir(), 'evm-eip712-mjs-'));
  const file = path.join(dir, 'index.mjs');
  await writeFile(file, body);
  relaxed = await import(pathToFileURL(file).href);
  return relaxed;
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
  /** The local Zswap commitment tree (default: empty). */
  zswap?: ZswapChainState;
  /** The coin store the held_coin witness answers from (default: empty). */
  privateState?: CoinStorePrivateState;
  /** Build calls as the local wallet `localKeys` (needed for outputs to a
   *  user's Zswap key); default: the all-zero keys. */
  withKeys?: boolean;
}

/** A deterministic local wallet (coin and encryption keys) for shielded
 *  outputs to a user's key. */
export const localKeys = ZswapSecretKeys.fromSeed(new Uint8Array(32).fill(0x5a));
export const localCoinPublicKeyBytes = (): Uint8Array => new Uint8Array(Buffer.from(String(localKeys.coinPublicKey), 'hex'));

const hexOf = (b: Uint8Array) => Buffer.from(b).toString('hex');

export interface LocalCoin { nonce: Uint8Array; color: Uint8Array; value: bigint; mtIndex: bigint }

/** Inserts contract-owned coins of `a` into its local Zswap tree, in order;
 *  returns each coin with the Merkle index it received. */
export function withLocalCoins(a: LocalAccount, coins: { nonce: Uint8Array; color: Uint8Array; value: bigint }[]): { account: LocalAccount; coins: LocalCoin[] } {
  let st = a.zswap ?? new ZswapChainState();
  const out: LocalCoin[] = [];
  for (const c of coins) {
    const info = { type: hexOf(c.color), nonce: hexOf(c.nonce), value: c.value } as any;
    const o = ZswapOutput.newContractOwned(info, 0, a.contractAddress as any);
    const at = st.firstFree;
    const [next, inserted] = st.tryApply(ZswapOffer.fromOutput(o as any, info.type, info.value));
    const idx = inserted.get(o.commitment) ?? at;
    if (next.firstFree !== at + 1n) throw new Error('withLocalCoins: the coin was not inserted into the local tree');
    st = next;
    out.push({ ...c, mtIndex: idx });
  }
  return { account: { ...a, zswap: st, withKeys: true }, coins: out };
}

/** A coin store whose `held_coin(color)` answers `coin` for each listed
 *  colour key (the coin's own colour may differ: witness substitution). */
export function coinStoreAnswering(entries: { key: Uint8Array; coin: LocalCoin }[]): CoinStorePrivateState {
  const s = emptyCoinStore(new Uint8Array(32).fill(7));
  for (const { key, coin } of entries) {
    s.coins[hexOf(key)] = { nonceHex: hexOf(coin.nonce), colorHex: hexOf(coin.color), value: coin.value.toString(), mtIndex: coin.mtIndex.toString() };
  }
  return s;
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
  // a direct transfer's first half (see relaxedContractsModule)
  const build = /_to_contract_with_/.test(circuitId)
    ? (await relaxedContractsModule()).createUnprovenCallTxFromInitialStates
    : createUnprovenCallTxFromInitialStates;
  const call: any = await build(zk as any, {
    compiledContract: compiled(C), circuitId, contractAddress: a.contractAddress,
    coinPublicKey: a.withKeys ? localKeys.coinPublicKey : coinPublicKey,
    initialContractState: a.state, initialZswapChainState: a.zswap ?? new ZswapChainState(),
    ledgerParameters: LedgerParameters.initialParameters(), args, initialPrivateState: a.privateState ?? privateState,
  } as any, a.withKeys ? localKeys.encryptionPublicKey : encryptionPublicKey);
  const next = ContractState.deserialize(a.state.serialize());
  next.data = new ChargedState(call.public.nextContractState);
  return { call, after: { ...a, state: next } as LocalAccount };
}

/** Transport retries of `prove` (see below), for the evidence. */
export const transportRetries: { circuitId: string; attempt: number; error: string; at: string }[] = [];

/** Executes locally, then proves the call at the proof server.
 *
 *  A TRANSPORT failure (the request never reached the proof server or got no
 *  HTTP answer: "fetch failed", EPIPE, ECONNRESET — seen when uploading
 *  prover keys of a few hundred MB: the upload breaks with EPIPE about half
 *  a second in and the proof server never logs the request) is retried, at
 *  most four times, 20 s apart, and recorded in `transportRetries`. Nothing
 *  else is retried: an HTTP answer (a refusal) is final, and a fifth
 *  transport failure is thrown and classified as infrastructure (ERROR),
 *  never a pass. */
export async function prove(C: any, a: LocalAccount, circuitId: string, args: unknown[]) {
  const { call, after } = await execute(C, a, circuitId, args);
  for (let attempt = 1; ; attempt++) {
    const before = proofLog.length;
    try {
      const proven = await proofProvider.proveTx({ version: 'v9', tx: call.private.unprovenTx } as any);
      return { proven, after };
    } catch (e: any) {
      const answered = proofLog.slice(before).some((q) => q.status !== null && !q.ok);
      const text = String(e?.message ?? e) + ' ' + String(e?.cause?.message ?? '') + ' ' + String(e?.cause?.code ?? '');
      const transport = !answered && /fetch failed|epipe|econnreset|socket hang up|other side closed/i.test(text);
      if (!transport || attempt >= 5) throw e;
      transportRetries.push({ circuitId, attempt, error: text.slice(0, 300), at: new Date().toISOString() });
      await new Promise((r) => setTimeout(r, 20_000));
    }
  }
}
