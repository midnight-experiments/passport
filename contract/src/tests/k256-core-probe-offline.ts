// The k256 core on its own (contracts/probe-k256-core.compact), at the
// offline layer: the compact-runtime local simulator (the generated
// JavaScript), with no node and no proof server. Through an arm, the core's
// key rule cannot be observed (the arm derives the key's address first, and
// that already fails for the point at infinity), so this suite calls the
// core directly, through the probe's impure circuits and its pure re-exports:
//
//   - honest controls: a key's low-S signature and its high-S twin verify;
//     a signature by another key, or over another digest, does not (the
//     verification returns false, the call lands); a live key is admitted
//     by the key rule;
//   - the point at infinity as the key, in both encodings (flagged, and the
//     unflagged (0, 0)), is refused by the key rule and by the verification,
//     with the signature that verifies against it when its term vanishes:
//     digest = 1, s = 1, r = x(G) (u1·G + u2·O = G);
//   - r = 0, s = 0 and (0, 0) are refused, with the honest key and digest;
//   - a digest hint that is not the digest's bytes is refused.
// A refused call must leave the ledger untouched (atomic abort).
//
// Writes $EVIDENCE_DIR/k256-core-probe-offline.json when EVIDENCE_DIR is set.

import { createHash } from 'node:crypto';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { createCircuitContext, createConstructorContext, sampleContractAddress } from '@midnight-ntwrk/compact-runtime';
import * as Probe from '../../contracts/managed/probe-k256-core/contract/index.js';

const SEED = 'k256-core-probe-offline/v1';
let ctr = 0;
const rnd = (n = 32): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
const beInt = (b: Uint8Array) => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const be32 = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const hint = (b: Uint8Array) => Array.from(b, (x) => BigInt(x));
const N = secp256k1.Point.Fn.ORDER;
const G = secp256k1.Point.BASE.toAffine();

type Point = { x: bigint; y: bigint; identity: boolean };
type Sig = { r: bigint; s: bigint };
const pointOf = (sk: bigint): Point => { const p = secp256k1.Point.BASE.multiply(sk).toAffine(); return { x: p.x, y: p.y, identity: false }; };
const signOf = (sk: bigint, digest: Uint8Array): Sig => {
  const sig = secp256k1.Signature.fromBytes(secp256k1.sign(digest, be32(sk), { prehash: false, format: 'compact' }), 'compact');
  return { r: sig.r, s: sig.s };
};

// ── Reporting ───────────────────────────────────────────────────────────────

let pass = 0, fail = 0;
const failures: string[] = [];
const refusals: { label: string; message: string }[] = [];
function ok(condition: boolean, label: string) {
  if (condition) { pass++; console.log(`  ✓ ${label}`); } else { fail++; failures.push(label); console.log(`  ✗ ${label}`); }
}

// ── The simulated probe ─────────────────────────────────────────────────────

const contract: any = new (Probe.Contract as any)({});
const impure: Record<string, (...a: any[]) => Promise<any>> = contract.impureCircuits;
const pure: any = Probe.pureCircuits;
const coinPk = { bytes: rnd() };
const addressHex: string = sampleContractAddress();
const init = await contract.initialState(createConstructorContext({}, coinPk));
let state: any = init.currentContractState;
const L = () => Probe.ledger(state) as any;
const fingerprint = () => JSON.stringify({ verified: L().verified, admitted: L().keys_admitted }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v));

async function call(name: string, args: unknown[]) {
  const ctx: any = createCircuitContext({ circuitId: name, contractAddress: addressHex, coinPublicKeyOrZswapState: coinPk,
    contractState: state, privateState: {}, time: 1_800_000_000 } as any);
  const res = await impure[name](ctx, ...args);
  state = res.context.callContext.currentQueryContext.state;
  return res;
}
const verify = (digest: Uint8Array, sig: Sig, pk: Point, h = hint(digest)) => call('probe_k256_ecdsa_verify', [digest, h, sig, pk]);
const admit = (pk: Point) => call('probe_k256_require_live_key', [pk]);

/** The call must be refused, leave the ledger untouched, and the pure
 *  circuit must refuse the same input (when `pureCall` is given). */
async function refused(label: string, f: () => Promise<unknown>, pureCall?: () => unknown) {
  const before = fingerprint();
  try { await f(); ok(false, `${label} (NOT refused: the core accepted it)`); }
  catch (e: any) { refusals.push({ label, message: String(e?.message ?? e).slice(0, 240) }); ok(true, `${label}: refused`); }
  ok(fingerprint() === before, `${label}: the ledger is unchanged (atomic abort)`);
  if (pureCall) {
    try { const r = pureCall(); ok(false, `${label} (pure circuit NOT refused: returned ${String(r)})`); }
    catch (e: any) { refusals.push({ label: `${label} (pure)`, message: String(e?.message ?? e).slice(0, 240) }); ok(true, `${label}: refused by the pure circuit too`); }
  }
}

// ── Honest controls ─────────────────────────────────────────────────────────

const sk = beInt(rnd()) % (N - 1n) + 1n, other = beInt(rnd()) % (N - 1n) + 1n;
const pk = pointOf(sk), pkOther = pointOf(other);
const digest = rnd();
const sig = signOf(sk, digest);
const twin = { r: sig.r, s: N - sig.s };
console.log('── honest controls');
ok(sig.s <= N / 2n && twin.s > N / 2n, 'the control signature is low-S and its twin high-S');
await verify(digest, sig, pk);
ok(L().verified === true, 'a key\'s low-S signature verifies');
await verify(digest, { r: 1n, s: 1n }, pk);
ok(L().verified === false, 'the ledger cell follows the result (a non-verifying call lands with false)');
await verify(digest, twin, pk);
ok(L().verified === true, 'its high-S twin verifies (both S forms are accepted)');
await verify(digest, signOf(other, digest), pk);
ok(L().verified === false, 'another key\'s signature does not verify (the call lands, false)');
const digest2 = rnd();
await verify(digest2, sig, pk);
ok(L().verified === false, 'the signature over another digest does not verify');
ok(pure.k256_ecdsa_verify(digest, hint(digest), sig, pk) === true && pure.k256_ecdsa_verify(digest, hint(digest), sig, pkOther) === false,
  'the pure re-export: true for the honest triple, false under another key');
const before = L().keys_admitted;
await admit(pk);
await admit(pkOther);
ok(L().keys_admitted === before + 2n, 'the key rule admits two live keys');

// ── The point at infinity as the key ────────────────────────────────────────

// With Q = O the key's term vanishes: u1 = z/s = 1, so x(u1·G + u2·Q) = x(G),
// and r = x(G) (below n) passes the final comparison without a private key.
const one = be32(1n);
const forged: Sig = { r: G.x % N, s: 1n };
ok(G.x < N && secp256k1.Point.BASE.multiply(1n).toAffine().x % N === forged.r, 'the construction: r = x(G) = x(1·G) mod n, so only the key rule stands in its way');
const O_FLAGGED: Point = { x: 0n, y: 0n, identity: true };
const O_ZERO: Point = { x: 0n, y: 0n, identity: false };
console.log('── the point at infinity');
for (const [name, O] of [['flagged', O_FLAGGED], ['unflagged (0, 0)', O_ZERO]] as const) {
  await refused(`the key rule refuses the point at infinity (${name})`, () => admit(O), () => pure.k256_require_live_key(O));
  await refused(`the verification refuses the point at infinity (${name}) with digest 1, s = 1, r = x(G)`,
    () => verify(one, forged, O), () => pure.k256_ecdsa_verify(one, hint(one), forged, O));
}

// ── Zero scalars ────────────────────────────────────────────────────────────

console.log('── zero scalars');
await refused('r = 0 is refused at the core (the honest key, digest and s)', () => verify(digest, { r: 0n, s: sig.s }, pk), () => pure.k256_ecdsa_verify(digest, hint(digest), { r: 0n, s: sig.s }, pk));
await refused('s = 0 is refused at the core (the honest key, digest and r)', () => verify(digest, { r: sig.r, s: 0n }, pk), () => pure.k256_ecdsa_verify(digest, hint(digest), { r: sig.r, s: 0n }, pk));
await refused('(r, s) = (0, 0) is refused at the core', () => verify(digest, { r: 0n, s: 0n }, pk), () => pure.k256_ecdsa_verify(digest, hint(digest), { r: 0n, s: 0n }, pk));

// ── The digest hint ─────────────────────────────────────────────────────────

console.log('── the digest hint');
await refused('a digest hint that is not the digest\'s bytes is refused', () => verify(digest, sig, pk, hint(digest2)), () => pure.k256_ecdsa_verify(digest, hint(digest2), sig, pk));

// the honest call still lands after the refusals
await verify(digest, sig, pk);
ok(L().verified === true, 'the honest call lands after the refusals');

const verdict = fail === 0 && pass > 0 ? 'PASS' : 'FAIL';
console.log(`\n◆ k256-core-probe-offline: ${verdict} (${pass} passed, ${fail} failed)`);
if (process.env.EVIDENCE_DIR) {
  const fs = await import('node:fs');
  fs.writeFileSync(`${process.env.EVIDENCE_DIR}/k256-core-probe-offline.json`, JSON.stringify({ suite: 'k256-core-probe-offline', ranAt: new Date().toISOString(),
    layer: 'runtime (generated JavaScript, compact-runtime simulator)', pass, fail, failures, refusals, verdict }, null, 2) + '\n');
}
process.exit(verdict === 'PASS' ? 0 : 1);
