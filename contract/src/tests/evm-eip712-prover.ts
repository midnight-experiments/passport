// Constraint-level negatives of the `evm_eip712` arm (spec FR-019), on local
// account states (no deploy, no node, no wallet), proved at the proof server.
//
// For every case:
//   positive   an honest call through the PATCHED module (the negatives' own
//              path) is proved by the proof server — the path works, so a
//              refusal is the tampering's;
//   simulator  the bad call, executed with the ORIGINAL module, is refused by
//              the generated JavaScript (or the runtime's own type checks);
//   prover     the bad call, executed with the named asserts bypassed (and,
//              where a degenerate value must reach the transcript, the
//              runtime's validators relaxed), is refused by the proof server:
//              the rule is a constraint of the proof.
//
// Sections (all by default; or name them on the command line):
//   activation  (S2E) wrong blind, wrong address, the point at infinity in
//               both encodings;
//   reactivation (S5E) activating an account that is already booted;
//   qa1         (S5E, audit QA-1) a point whose coordinate is not reduced
//               below the base-field modulus, at the representation boundary;
//   seam        (S5E) rotate_enc_key_with_evm_eip712: the binding matrix
//               (every signed member changed after signing), the
//               authorisation fields, the zero and degenerate signatures, and
//               the replay matrix (account, arm, operation, role, nonce),
//               with the high-S twin as a positive and the original refused
//               after it.
//
// Needs a proof server at upstream's endpoint (CONFIG.proofServer); a missing
// proof server is an ERROR, never a pass. Writes
// $EVIDENCE_DIR/evm-eip712-prover[-<sections>].json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { createHash } from 'node:crypto';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { CONFIG } from '../node/wallet.js';
import { JubjubDevice, K256Device, k256Challenges } from '../wallet/signer.js';
import { SoftwareEvmWallet, EvmEip712Device, highSTwin, parseEvmSignature, serialiseEvmSignature } from '../wallet/signer-evm-eip712.js';
import { evmEip712Messages, typedDataDigest, type Eip712TypedData } from '../wallet/evm-eip712-codec.js';
import { expectRefusal, expectSuccess, type NegativeResult, type PositiveResult } from './constraint-negative.js';
import {
  Original, loadPatched, dormant, execute, prove, ledgerOf, proofLog,
  POINT_AT_INFINITY_OVERRIDES, NON_CANONICAL_COORDINATE_OVERRIDES, type LocalAccount,
} from './evm-eip712-negative.js';

const SECTIONS = process.argv.slice(2).length ? process.argv.slice(2) : ['activation', 'reactivation', 'qa1', 'seam'];
const SEED = 'aa00067/e/s5/evm-eip712-prover/v1';
let ctr = 0;
const rnd = (n: number) => new Uint8Array(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, n));
const pc = Original.pureCircuits;
const recoveryPk = JubjubDevice.generate().pk;

const ACTIVATE = 'activate_initial_device_with_evm_eip712';
const ROTATE = 'rotate_enc_key_with_evm_eip712';
const INFINITY = 'evm_eip712: device key is the point at infinity';
const STDLIB_ADDR_IDENTITY = 'Secp256k1Point identity is not a permitted input to secp256k1EthereumAddress';
const STDLIB_VERIFY_IDENTITY = 'Secp256k1Point identity is not a permitted secp256k1EcdsaVerify verification key';
const BOOT = 'boot commitment mismatch';
const UNKNOWN = 'unknown device entry';
const INVALID = 'invalid signature';
const ZERO = 'evm_eip712: signature scalar is zero';
const K256_INVALID = 'invalid signature';

interface Result { section: string; circuit: string; case: string; kind: 'positive' | 'negative'; expect?: string; bypassed?: string[];
  overrides?: string; positive?: PositiveResult; simulator?: NegativeResult; prover?: NegativeResult }
const results: Result[] = [];
let failures = 0, errors = 0;
const tally = (...r: (PositiveResult | NegativeResult | undefined)[]) => {
  for (const x of r) { if (!x) continue; if (x.verdict === 'FAIL') failures++; if (x.verdict === 'ERROR') errors++; }
};
const line = (r: Result) => {
  const parts = [r.positive && `positive ${r.positive.verdict}`, r.simulator && `simulator ${r.simulator.verdict}`, r.prover && `prover ${r.prover.verdict} (${r.prover.layer}${r.prover.proofServer.at(-1)?.status ? `, ${r.prover.proofServer.at(-1)!.endpoint} ${r.prover.proofServer.at(-1)!.status}` : ''})`].filter(Boolean);
  const okAll = [r.positive, r.simulator, r.prover].every((x) => !x || x.verdict === 'PASS');
  console.log(`  ${okAll ? '✓' : '✗'} [${r.section}] ${r.case}: ${parts.join(', ')}`);
  for (const [k, x] of [['positive', r.positive], ['simulator', r.simulator], ['prover', r.prover]] as const) {
    if (x && x.verdict !== 'PASS') console.log(`      ${k}: ${x.reason} ${(x as any).detail ?? ''}`.slice(0, 600));
  }
};

/** One positive control: the honest call through a patched module proves. */
async function positive(section: string, name: string, C: any, a: LocalAccount, circuit: string, args: unknown[]) {
  const r: Result = { section, circuit, case: name, kind: 'positive' };
  r.positive = await expectSuccess({ name: `${circuit}: ${name}`, proofLog, attempt: () => prove(C, a, circuit, args) });
  r.positive = { ...r.positive, result: undefined };
  tally(r.positive); results.push(r); line(r);
  return r.positive.verdict === 'PASS';
}

/** One negative: refused by the simulator, and by the prover with `bypass`. */
async function negative(section: string, name: string, a: LocalAccount, circuit: string, args: unknown[],
  expect: string, bypass: string[], overrides = '') {
  const r: Result = { section, circuit, case: name, kind: 'negative', expect, bypassed: bypass, overrides: overrides ? 'runtime validators relaxed' : undefined };
  r.simulator = await expectRefusal({ name: `${circuit}: ${name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog,
    attempt: () => execute(Original.Contract, a, circuit, args) });
  if (r.simulator.verdict === 'PASS' && !String(r.simulator.detail ?? '').includes(expect)) {
    r.simulator.verdict = 'FAIL'; r.simulator.reason = `refused at runtime, but not by "${expect}"`;
  }
  const patched = await loadPatched(bypass, overrides);
  r.prover = await expectRefusal({ name: `${circuit}: ${name} (JavaScript checks bypassed)`, expectedLayer: 'prover', bypassed: patched, proofLog,
    attempt: () => prove(patched.Contract, a, circuit, args) });
  tally(r.simulator, r.prover); results.push(r); line(r);
}

// ═════════════════════════════════════════════════════════════════════════════
// The device and its accounts
// ═════════════════════════════════════════════════════════════════════════════

const SK = 0xa11ce5n;
const wallet = new SoftwareEvmWallet(SK);
const device = await EvmEip712Device.enrol(wallet, 'undeployed', 0);
const device1 = await EvmEip712Device.enrol(wallet, 'undeployed', 1);
const other = new SoftwareEvmWallet(0xb0bn);
const salt = rnd(32);

// ── activation (S2E) ─────────────────────────────────────────────────────────
if (SECTIONS.includes('activation')) {
  const honestBoot = device.bootCommitment(salt);
  const infinityAddress = keccak_256(new Uint8Array(64)).subarray(12);
  const infinityBoot = pc.derive_boot_commitment_with_evm_eip712(salt, infinityAddress, device.blind);
  const all = await loadPatched([BOOT, INFINITY, STDLIB_ADDR_IDENTITY], POINT_AT_INFINITY_OVERRIDES);
  await positive('activation', 'honest activation (patched path)', all.Contract, await dormant(honestBoot, recoveryPk), ACTIVATE, device.activationArgs(salt));
  await negative('activation', 'wrong blind', await dormant(honestBoot, recoveryPk), ACTIVATE, [device.pk, salt, rnd(32)], BOOT, [BOOT]);
  await negative('activation', 'wrong address (another key, the committed blind)', await dormant(honestBoot, recoveryPk), ACTIVATE, [other.pk, salt, device.blind], BOOT, [BOOT]);
  await negative('activation', 'point at infinity, flagged {0, 0, identity}', await dormant(infinityBoot, recoveryPk), ACTIVATE,
    [{ x: 0n, y: 0n, identity: true }, salt, device.blind], 'identity point', [INFINITY, STDLIB_ADDR_IDENTITY], POINT_AT_INFINITY_OVERRIDES);
  await negative('activation', 'point at infinity, unflagged {0, 0, not identity}', await dormant(infinityBoot, recoveryPk), ACTIVATE,
    [{ x: 0n, y: 0n, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [INFINITY], POINT_AT_INFINITY_OVERRIDES);
}

// ── reactivation (S5E) ──────────────────────────────────────────────────────
if (SECTIONS.includes('reactivation')) {
  const ALREADY = 'already activated';
  const fresh = await dormant(device.bootCommitment(salt), recoveryPk);
  const patched = await loadPatched([ALREADY, BOOT]);
  await positive('reactivation', 'first activation (patched path)', patched.Contract, fresh, ACTIVATE, device.activationArgs(salt));
  const booted = (await execute(Original.Contract, fresh, ACTIVATE, device.activationArgs(salt))).after;
  // the same device again (its boot commitment was cleared: two asserts fail)
  await negative('reactivation', 'activate a booted account again (same device)', booted, ACTIVATE, device.activationArgs(salt), ALREADY, [ALREADY, BOOT]);
}

// ── QA-1: coordinates not reduced below p (S5E) ─────────────────────────────
//
// A secp256k1 point with a small coordinate c < 2^256 - p, presented as
// c + p: the same field element, a non-canonical representation. The boot
// commitment is made to the address a NON-reducing byte conversion would give
// (keccak256(be(c + p) || be(other))[12..]), so if the proof accepted the
// unreduced limbs as bytes, activation would go through; it must not.
if (SECTIONS.includes('qa1')) {
  const { secp256k1 } = await import('@noble/curves/secp256k1.js');
  const P = secp256k1.Point.Fp.ORDER;
  const be = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
  const smallX = (() => { for (let x = 1n; ; x++) { try { const pt = secp256k1.Point.fromAffine({ x, y: secp256k1.Point.Fp.sqrt((x ** 3n + 7n) % P) }); pt.assertValidity(); return pt.toAffine(); } catch { /* next */ } } })();
  // (A y + p case needs a point with y < 2^32 + 977, i.e. a cube root mod p;
  // the x + p case alone exercises the representation boundary.)
  const cases: [string, { x: bigint; y: bigint }, { x: bigint; y: bigint }][] = [['x + p', smallX, { x: smallX.x + P, y: smallX.y }]];
  for (const [label, real, shifted] of cases) {
    const naiveAddress = keccak_256(new Uint8Array([...be(shifted.x), ...be(shifted.y)])).subarray(12);
    const naiveBoot = pc.derive_boot_commitment_with_evm_eip712(salt, naiveAddress, device.blind);
    const realBoot = pc.derive_boot_commitment_with_evm_eip712(salt, keccak_256(new Uint8Array([...be(real.x), ...be(real.y)])).subarray(12), device.blind);
    const patched = await loadPatched([BOOT], NON_CANONICAL_COORDINATE_OVERRIDES);
    await positive('qa1', `canonical point with a small coordinate (${label.split(' ')[0]} = ${label.startsWith('x') ? real.x : real.y}) activates (patched path)`,
      patched.Contract, await dormant(realBoot, recoveryPk), ACTIVATE, [{ ...real, identity: false }, salt, device.blind]);
    // Here the generated JavaScript computes the unreduced bytes too, so no
    // assert needs bypassing: only the validators are relaxed.
    await negative('qa1', `non-canonical ${label}: boot commitment to the unreduced bytes`, await dormant(naiveBoot, recoveryPk), ACTIVATE,
      [{ ...shifted, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [], NON_CANONICAL_COORDINATE_OVERRIDES);
    await negative('qa1', `non-canonical ${label}: boot commitment to the real address`, await dormant(realBoot, recoveryPk), ACTIVATE,
      [{ ...shifted, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [BOOT], NON_CANONICAL_COORDINATE_OVERRIDES);
  }
}

// ── The seam: rotate_enc_key_with_evm_eip712 (S5E) ──────────────────────────
if (SECTIONS.includes('seam')) {
  // Account A: the device at index 0. Account B: the same wallet at index 1
  // (another account, another blind). Account K: the same secret key enrolled
  // on the k256 arm (envelope 0).
  const A0 = (await execute(Original.Contract, await dormant(device.bootCommitment(salt), recoveryPk), ACTIVATE, device.activationArgs(salt))).after;
  const B0 = (await execute(Original.Contract, await dormant(device1.bootCommitment(salt), recoveryPk), ACTIVATE, device1.activationArgs(salt))).after;
  const k1 = new K256Device(SK);
  const K0 = (await execute(Original.Contract, await dormant(k1.bootCommitment(salt), recoveryPk), 'activate_initial_device_with_k256', [k1.pk, salt, 0n])).after;
  const newKey = rnd(32), otherKey = rnd(32);
  const ctxOf = (a: LocalAccount, d: EvmEip712Device) => ({ account: a.addressBytes, device: d.address, authNonce: ledgerOf(a).auth_nonce as bigint });
  const td = (a: LocalAccount, key = newKey) => evmEip712Messages.rotateEncKey(ctxOf(a, device), key);
  const sign = (t: Eip712TypedData) => wallet.signDigest(typedDataDigest(t));
  const authOf = (sig: Uint8Array, counter = 0n, d = device) => {
    const p = parseEvmSignature(sig);
    return { pk: d.pk, use_counter: counter, blind: d.blind, sig: { r: p.r, s: p.s } };
  };
  const honest = authOf(sign(td(A0)));
  const mutate = (f: (t: any) => void) => { const t = JSON.parse(JSON.stringify(td(A0))); f(t); return authOf(sign(t)); };
  const rename = (t: any, from: string, to: string) => {
    t.types[to] = t.types[from]; delete t.types[from]; t.primaryType = to;
  };
  const posPath = await loadPatched([INVALID, UNKNOWN, ZERO]);

  // positives: the honest call and its high-S twin, both from A0
  await positive('seam', 'honest rotate_enc_key (patched path)', posPath.Contract, A0, ROTATE, [newKey, honest]);
  const twinSig = highSTwin(parseEvmSignature(sign(td(A0))));
  const twin = { ...honest, sig: { r: twinSig.r, s: twinSig.s } };
  await positive('seam', 'the high-S twin of the honest signature', posPath.Contract, A0, ROTATE, [newKey, twin]);
  const K256_ROT = 'rotate_enc_key_with_k256';
  const kAuth = k1.sign(k256Challenges.rotateEncKey({ contractAddress: K0.addressBytes, authNonce: 0n }, k1.pk, newKey), 0n);
  await positive('seam', 'honest k256 rotate on account K (the cross-arm control)', posPath.Contract, K0, K256_ROT, [newKey, kAuth.pk, 0n, kAuth.sig, 0n]);

  // binding matrix: every signed member, changed after signing
  const B: [string, any][] = [
    ['newKey: signed K\', executed K', authOf(sign(td(A0, otherKey)))],
    ['account member: another account', mutate((t) => { t.message.account = '0x' + Buffer.from(B0.addressBytes).toString('hex'); })],
    ['device member: another address', mutate((t) => { t.message.device = '0x' + Buffer.from(other.addressBytes).toString('hex'); })],
    ['authNonce: n + 1', mutate((t) => { t.message.authNonce = '1'; })],
    ['effect line: another text', mutate((t) => { t.message.effect = 'Sets nothing'; })],
    ['domain name', mutate((t) => { t.domain.name = 'Midnight Passport Accounts'; })],
    ['domain version', mutate((t) => { t.domain.version = '1'; })],
    ['domain verifyingContract', mutate((t) => { t.domain.verifyingContract = '0x' + Buffer.from(rnd(20)).toString('hex'); })],
    ['primary type name', mutate((t) => rename(t, 'RotateEncKey', 'RotateEncryptionKey'))],
    ['a member renamed (newKey -> key)', mutate((t) => { t.types.RotateEncKey = t.types.RotateEncKey.map((f: any) => (f.name === 'newKey' ? { ...f, name: 'key' } : f)); t.message.key = t.message.newKey; delete t.message.newKey; })],
  ];
  for (const [name, auth] of B) await negative('seam', `binding: ${name}`, A0, ROTATE, [newKey, auth], INVALID, [INVALID]);

  // the authorisation fields and degenerate signatures
  await negative('seam', 'auth: an unenrolled key signs the right message', A0, ROTATE,
    [newKey, { pk: other.pk, use_counter: 0n, blind: device.blind, sig: authOf(other.signDigest(typedDataDigest(evmEip712Messages.rotateEncKey({ ...ctxOf(A0, device), device: other.addressBytes }, newKey)))).sig }], UNKNOWN, [UNKNOWN]);
  await negative('seam', 'auth: the right key with another blind', A0, ROTATE, [newKey, { ...honest, blind: device1.blind }], UNKNOWN, [UNKNOWN]);
  await negative('seam', 'auth: a wrong use counter', A0, ROTATE, [newKey, { ...honest, use_counter: 1n }], UNKNOWN, [UNKNOWN]);
  await negative('seam', 'signature r = 0', A0, ROTATE, [newKey, { ...honest, sig: { r: 0n, s: honest.sig.s } }], ZERO, [ZERO, INVALID]);
  await negative('seam', 'signature s = 0', A0, ROTATE, [newKey, { ...honest, sig: { r: honest.sig.r, s: 0n } }], ZERO, [ZERO, INVALID],
    `secp256k1ScalarInv(x) { return x === 0n ? 0n : __compactRuntimeOriginal.secp256k1ScalarInv(x); },
  secp256k1PointX(p) { return p && p.identity ? 0n : __compactRuntimeOriginal.secp256k1PointX(p); },`);
  await negative('seam', '(r, s) = (0, 0), which verifies against the identity point when inverses of 0 are taken as 0', A0, ROTATE,
    [newKey, { ...honest, sig: { r: 0n, s: 0n } }], ZERO, [ZERO],
    `secp256k1ScalarInv(x) { return x === 0n ? 0n : __compactRuntimeOriginal.secp256k1ScalarInv(x); },
  secp256k1PointX(p) { return p && p.identity ? 0n : __compactRuntimeOriginal.secp256k1PointX(p); },`);
  await negative('seam', 'device key = the point at infinity (flagged)', A0, ROTATE,
    [newKey, { ...honest, pk: { x: 0n, y: 0n, identity: true } }], 'identity point', [INFINITY, STDLIB_ADDR_IDENTITY, UNKNOWN, STDLIB_VERIFY_IDENTITY, INVALID], POINT_AT_INFINITY_OVERRIDES);

  // replay matrix
  await negative('seam', 'replay/account: a signature for account B executed on account A', A0, ROTATE,
    [newKey, authOf(sign(evmEip712Messages.rotateEncKey(ctxOf(B0, device1), newKey)))], INVALID, [INVALID]);
  await negative('seam', 'replay/arm: the EIP-712 signature presented to the k256 arm', K0, K256_ROT,
    [newKey, k1.pk, 0n, authOf(sign(td(K0))).sig, 0n], K256_INVALID, [K256_INVALID]);
  const k256OnA = k1.sign(k256Challenges.rotateEncKey({ contractAddress: A0.addressBytes, authNonce: 0n }, k1.pk, newKey), 0n);
  await negative('seam', 'replay/arm: a k256 signature for the same key presented to the evm arm', A0, ROTATE, [newKey, { ...honest, sig: k256OnA.sig }], INVALID, [INVALID]);
  await negative('seam', 'replay/operation: a CancelRecovery signature (same frame)', A0, ROTATE,
    [newKey, authOf(sign(evmEip712Messages.cancelRecovery(ctxOf(A0, device))))], INVALID, [INVALID]);
  await negative('seam', 'replay/operation: a RevokeAllGrants signature (same frame)', A0, ROTATE,
    [newKey, authOf(sign(evmEip712Messages.revokeAllGrants(ctxOf(A0, device))))], INVALID, [INVALID]);
  const lbl = new Uint8Array(32); lbl.set(new TextEncoder().encode('Midnight'));
  await negative('seam', 'replay/role: a grantee-role signature by the same key', A0, ROTATE,
    [newKey, authOf(sign(evmEip712Messages.withdrawUnshieldedAsGrantee({ account: A0.addressBytes, grantee: device.address, label: lbl, slot: 0n, issuedAt: 0n, grantNonce: 0n }, rnd(32), 1n, rnd(32))))], INVALID, [INVALID]);
  // nonce: after one honest rotate (A1: counter 1, auth_nonce 1)
  const A1 = (await execute(Original.Contract, A0, ROTATE, [newKey, twin])).after;
  if (ledgerOf(A1).auth_nonce !== 1n) throw new Error('setup: the twin did not advance auth_nonce');
  await positive('seam', 'the next honest rotate on A1 (counter 1, nonce 1)', posPath.Contract, A1, ROTATE, [otherKey, authOf(sign(evmEip712Messages.rotateEncKey(ctxOf(A1, device), otherKey)), 1n)]);
  // (its entry is consumed AND its message names the old nonce: both asserts fail)
  await negative('seam', 'replay/nonce: the low-S original after its high-S twin executed (entry consumed)', A1, ROTATE, [newKey, honest], UNKNOWN, [UNKNOWN, INVALID]);
  await negative('seam', 'replay/nonce: the old signature with the current counter (nonce advanced)', A1, ROTATE, [newKey, { ...honest, use_counter: 1n }], INVALID, [INVALID]);
}

const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  const suffix = process.argv.slice(2).length ? `-${process.argv.slice(2).join('-')}` : '';
  const file = path.join(process.env.EVIDENCE_DIR, `evm-eip712-prover${suffix}.json`);
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify({ suite: 'evm-eip712-prover', sections: SECTIONS, ranAt: new Date().toISOString(), proofServer: CONFIG.proofServer,
    device: { address: device.checksumAddress }, cases: results, requests: proofLog.length, verdict,
  }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ evm-eip712-prover [${SECTIONS.join(', ')}]: ${verdict} (${results.length} cases; ${failures} FAIL, ${errors} ERROR; ${proofLog.length} proof-server requests)`);
process.exit(verdict === 'PASS' ? 0 : 1);
