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
//               after it; a positive control through every runtime-override
//               module the seam's negatives use (audit F-A8);
//   frame       (G1E-1) the seam owns the frame: a malicious-prover mutant
//               forges the address the generated JavaScript derives from the
//               attacker's point (the victim's address, so the victim's entry
//               matches while the attacker's key signs), on every gated
//               export built so far; the proof must refuse it;
//   custody     (S6E) append_inbox and withdraw_unshielded: positives,
//               binding (each operand changed after signing), a cross-
//               operation replay, and the mirror's over-withdrawal;
//   witness     (S6E) withdraw_shielded and withdraw_shielded_to_contract on
//               a local Zswap tree: partial and full spends as positives, then
//               a valid signature over one coin with the held_coin witness
//               answering another (colour, value, nonce, Merkle index), the
//               Zswap half of the spend valid for the substituted coin, so
//               the refusing request must be the arm circuit's.
//
// Every prover-level negative records the refusing request's circuit (it must
// be the circuit under test) and the refusal's kind: `constraint` (the
// circuit's relation fails, e.g. "Failed direct assertion") or `decoding`
// (the honest proof server could not decode the preimage, which a malicious
// prover never runs; audit G1E-4). Each case names the kind it expects.
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
  Original, loadPatched, dormant, execute, prove, ledgerOf, proofLog, forgery, withLocalCoins, coinStoreAnswering,
  localCoinPublicKeyBytes, transportRetries, FORGE_ADDRESS_OVERRIDES, POINT_AT_INFINITY_OVERRIDES, NON_CANONICAL_COORDINATE_OVERRIDES, type LocalAccount, type LocalCoin,
} from './evm-eip712-negative.js';
import type { BypassedContractModule } from './constraint-negative.js';

const SECTIONS = process.argv.slice(2).length ? process.argv.slice(2) : ['activation', 'reactivation', 'qa1', 'seam', 'frame', 'custody', 'witness'];
const SEED = 'aa00067/e/s5/evm-eip712-prover/v1';
let ctr = 0;
const rnd = (n: number) => {
  const out = new Uint8Array(n);
  const tag = String(ctr++);
  // the first 32 bytes as the S5 runs drew them; more bytes, more blocks
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(tag).update(i ? `/${i}` : '').digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
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

type RefusalKind = 'constraint' | 'decoding';
interface Result { section: string; circuit: string; case: string; kind: 'positive' | 'negative'; expect?: string; bypassed?: string[];
  overrides?: string; positive?: PositiveResult; simulator?: NegativeResult; prover?: NegativeResult;
  refusal?: { circuit?: string; kind: RefusalKind | 'none'; rule?: string; expectedKind: RefusalKind }; mutant?: string }
const results: Result[] = [];
let failures = 0, errors = 0;
const tally = (...r: (PositiveResult | NegativeResult | undefined)[]) => {
  for (const x of r) { if (!x) continue; if (x.verdict === 'FAIL') failures++; if (x.verdict === 'ERROR') errors++; }
};
const line = (r: Result) => {
  const parts = [r.positive && `positive ${r.positive.verdict}`, r.simulator && `simulator ${r.simulator.verdict}`, r.prover && `prover ${r.prover.verdict} (${r.prover.layer}${r.prover.proofServer.at(-1)?.status ? `, ${r.prover.proofServer.at(-1)!.endpoint} ${r.prover.proofServer.at(-1)!.status}` : ''}${r.refusal ? `, ${r.refusal.kind}` : ''})`].filter(Boolean);
  const okAll = [r.positive, r.simulator, r.prover].every((x) => !x || x.verdict === 'PASS');
  console.log(`  ${okAll ? '✓' : '✗'} [${r.section}] ${r.case}: ${parts.join(', ')}`);
  for (const [k, x] of [['positive', r.positive], ['simulator', r.simulator], ['prover', r.prover]] as const) {
    if (x && x.verdict !== 'PASS') console.log(`      ${k}: ${x.reason} ${(x as any).detail ?? ''}`.slice(0, 600));
  }
};

/** One positive control: the honest call proved through `mod` (a patched
 *  copy, which records it as its positive control) or the original module. */
async function positive(section: string, name: string, mod: BypassedContractModule | undefined, a: LocalAccount, circuit: string, args: unknown[]) {
  const r: Result = { section, circuit, case: name, kind: 'positive' };
  r.positive = await expectSuccess({ name: `${circuit}: ${name}`, proofLog, through: mod,
    attempt: () => prove(mod ? mod.Contract : Original.Contract, a, circuit, args) });
  r.positive = { ...r.positive, result: undefined };
  tally(r.positive); results.push(r); line(r);
  return r.positive.verdict === 'PASS';
}

/** A negative that only the generated JavaScript can refuse, with the reason
 *  the prover level is unreachable from a JavaScript-built call (recorded,
 *  never counted as a constraint-level refusal). */
async function runtimeOnly(section: string, name: string, a: LocalAccount, circuit: string, args: unknown[], expect: string, why: string) {
  const r: Result = { section, circuit, case: name, kind: 'negative', expect };
  r.simulator = await expectRefusal({ name: `${circuit}: ${name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog,
    attempt: () => execute(Original.Contract, a, circuit, args) });
  if (r.simulator.verdict === 'PASS' && !String(r.simulator.detail ?? '').includes(expect)) {
    r.simulator.verdict = 'FAIL'; r.simulator.reason = `refused at runtime, but not by "${expect}"`;
  }
  (r as any).proverLevel = `not reachable from a JavaScript-built call: ${why}`;
  tally(r.simulator); results.push(r); line(r);
}

/** One negative: refused by the simulator, and by the proof server with
 *  `bypass` (or through `opts.module`, a mutant). At the proof server, the
 *  refusing request must be a recognised rejection (constraint-negative.ts)
 *  by `circuit`, of the expected kind: `constraint` (layer prover) or
 *  `decoding` (layer decoding, an honest-toolchain refusal). A copy with
 *  runtime overrides first proves `opts.control` (the honest call) through
 *  itself (FR-019, audit F-A8). */
async function negative(section: string, name: string, a: LocalAccount, circuit: string, args: unknown[],
  expect: string, bypass: string[], overrides = '',
  opts: { module?: BypassedContractModule; mutant?: string; kind?: RefusalKind; check?: () => string | undefined;
          control?: { a: LocalAccount; args: unknown[] } } = {}) {
  const r: Result = { section, circuit, case: name, kind: 'negative', expect, bypassed: bypass, overrides: overrides ? 'runtime validators relaxed' : undefined, mutant: opts.mutant };
  r.simulator = await expectRefusal({ name: `${circuit}: ${name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog,
    attempt: () => execute(Original.Contract, a, circuit, args) });
  if (r.simulator.verdict === 'PASS' && !String(r.simulator.detail ?? '').includes(expect)) {
    r.simulator.verdict = 'FAIL'; r.simulator.reason = `refused at runtime, but not by "${expect}"`;
  }
  const patched = opts.module ?? await loadPatched(bypass, overrides);
  const expectedKind = opts.kind ?? 'constraint';
  const control = opts.control;
  r.prover = await expectRefusal({ name: `${circuit}: ${name} (${opts.mutant ?? 'JavaScript checks bypassed'})`,
    expectedLayer: expectedKind === 'decoding' ? 'decoding' : 'prover', bypassed: patched, proofLog,
    positiveControl: control ? () => prove(patched.Contract, control.a, circuit, control.args) : undefined,
    attempt: () => prove(patched.Contract, a, circuit, args) });
  const rej = r.prover.rejection;
  r.refusal = { circuit: rej?.keyLocation, kind: rej ? rej.kind : 'none', rule: rej?.rule, expectedKind };
  if (r.prover.verdict === 'PASS') {
    // key locations read `contract:<address>/<circuit>?vk=<hash>`
    const refusedCircuit = rej?.keyLocation.match(/\/([A-Za-z0-9_]+)(\?|$)/)?.[1] ?? rej?.keyLocation;
    if (refusedCircuit !== circuit) { r.prover.verdict = 'FAIL'; r.prover.reason = `refused by ${rej?.keyLocation ?? 'no recorded request'}, not by ${circuit}`; }
    else { const bad = opts.check?.(); if (bad) { r.prover.verdict = 'FAIL'; r.prover.reason = bad; } }
  }
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
  await positive('activation', 'honest activation (patched path)', all, await dormant(honestBoot, recoveryPk), ACTIVATE, device.activationArgs(salt));
  const activationControl = { a: await dormant(honestBoot, recoveryPk), args: device.activationArgs(salt) };
  await negative('activation', 'wrong blind', await dormant(honestBoot, recoveryPk), ACTIVATE, [device.pk, salt, rnd(32)], BOOT, [BOOT]);
  await negative('activation', 'wrong address (another key, the committed blind)', await dormant(honestBoot, recoveryPk), ACTIVATE, [other.pk, salt, device.blind], BOOT, [BOOT]);
  await negative('activation', 'point at infinity, flagged {0, 0, identity}', await dormant(infinityBoot, recoveryPk), ACTIVATE,
    [{ x: 0n, y: 0n, identity: true }, salt, device.blind], 'identity point', [INFINITY, STDLIB_ADDR_IDENTITY], POINT_AT_INFINITY_OVERRIDES, { control: activationControl });
  await negative('activation', 'point at infinity, unflagged {0, 0, not identity} (honest-toolchain decoding refusal; in-circuit: the on-curve assignment)', await dormant(infinityBoot, recoveryPk), ACTIVATE,
    [{ x: 0n, y: 0n, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [INFINITY], POINT_AT_INFINITY_OVERRIDES, { kind: 'decoding', control: activationControl });
}

// ── reactivation (S5E) ──────────────────────────────────────────────────────
if (SECTIONS.includes('reactivation')) {
  const ALREADY = 'already activated';
  const fresh = await dormant(device.bootCommitment(salt), recoveryPk);
  const patched = await loadPatched([ALREADY, BOOT]);
  await positive('reactivation', 'first activation (patched path)', patched, fresh, ACTIVATE, device.activationArgs(salt));
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
      patched, await dormant(realBoot, recoveryPk), ACTIVATE, [{ ...real, identity: false }, salt, device.blind]);
    // Here the generated JavaScript computes the unreduced bytes too, so no
    // assert needs bypassing: only the validators are relaxed.
    // (G1E-4) these are honest-toolchain DECODING refusals, not constraint
    // refusals; the closure is the size argument (EVM-EIP712.md section 9).
    const qaControl = { a: await dormant(realBoot, recoveryPk), args: [{ ...real, identity: false }, salt, device.blind] };
    await negative('qa1', `non-canonical ${label}: boot commitment to the unreduced bytes`, await dormant(naiveBoot, recoveryPk), ACTIVATE,
      [{ ...shifted, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [], NON_CANONICAL_COORDINATE_OVERRIDES, { kind: 'decoding', control: qaControl });
    await negative('qa1', `non-canonical ${label}: boot commitment to the real address`, await dormant(realBoot, recoveryPk), ACTIVATE,
      [{ ...shifted, identity: false }, salt, device.blind], 'expected value of type Secp256k1Point', [BOOT], NON_CANONICAL_COORDINATE_OVERRIDES, { kind: 'decoding', control: qaControl });
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
  await positive('seam', 'honest rotate_enc_key (patched path)', posPath, A0, ROTATE, [newKey, honest]);
  const twinSig = highSTwin(parseEvmSignature(sign(td(A0))));
  const twin = { ...honest, sig: { r: twinSig.r, s: twinSig.s } };
  await positive('seam', 'the high-S twin of the honest signature', posPath, A0, ROTATE, [newKey, twin]);
  const K256_ROT = 'rotate_enc_key_with_k256';
  const kAuth = k1.sign(k256Challenges.rotateEncKey({ contractAddress: K0.addressBytes, authNonce: 0n }, k1.pk, newKey), 0n);
  await positive('seam', 'honest k256 rotate on account K (the cross-arm control)', posPath, K0, K256_ROT, [newKey, kAuth.pk, 0n, kAuth.sig, 0n]);

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
  // (F-A8) every runtime-override copy below first proves the honest call
  // through itself (the negative's positive control)
  const ZERO_INV_OVERRIDES = `secp256k1ScalarInv(x) { return x === 0n ? 0n : __compactRuntimeOriginal.secp256k1ScalarInv(x); },
  secp256k1PointX(p) { return p && p.identity ? 0n : __compactRuntimeOriginal.secp256k1PointX(p); },`;
  const seamControl = { a: A0, args: [newKey, honest] };
  await negative('seam', 'signature r = 0', A0, ROTATE, [newKey, { ...honest, sig: { r: 0n, s: honest.sig.s } }], ZERO, [ZERO, INVALID]);
  await negative('seam', 'signature s = 0', A0, ROTATE, [newKey, { ...honest, sig: { r: honest.sig.r, s: 0n } }], ZERO, [ZERO, INVALID], ZERO_INV_OVERRIDES, { control: seamControl });
  await negative('seam', '(r, s) = (0, 0), which verifies against the identity point when inverses of 0 are taken as 0', A0, ROTATE,
    [newKey, { ...honest, sig: { r: 0n, s: 0n } }], ZERO, [ZERO], ZERO_INV_OVERRIDES, { control: seamControl });
  await negative('seam', 'device key = the point at infinity (flagged)', A0, ROTATE,
    [newKey, { ...honest, pk: { x: 0n, y: 0n, identity: true } }], 'identity point', [INFINITY, STDLIB_ADDR_IDENTITY, UNKNOWN, STDLIB_VERIFY_IDENTITY, INVALID], POINT_AT_INFINITY_OVERRIDES, { control: seamControl });

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
  await positive('seam', 'the next honest rotate on A1 (counter 1, nonce 1)', posPath, A1, ROTATE, [otherKey, authOf(sign(evmEip712Messages.rotateEncKey(ctxOf(A1, device), otherKey)), 1n)]);
  // (its entry is consumed AND its message names the old nonce: both asserts fail)
  await negative('seam', 'replay/nonce: the low-S original after its high-S twin executed (entry consumed)', A1, ROTATE, [newKey, honest], UNKNOWN, [UNKNOWN, INVALID]);
  await negative('seam', 'replay/nonce: the old signature with the current counter (nonce advanced)', A1, ROTATE, [newKey, { ...honest, use_counter: 1n }], INVALID, [INVALID]);
}

// ═════════════════════════════════════════════════════════════════════════════
// S6E: custody, and G1E-1's frame mutant
// ═════════════════════════════════════════════════════════════════════════════

const APPEND = 'append_inbox_with_evm_eip712';
const WU = 'withdraw_unshielded_with_evm_eip712';
const WS = 'withdraw_shielded_with_evm_eip712';
const WSC = 'withdraw_shielded_to_contract_with_evm_eip712';
const COLOUR = 'held coin colour does not match the withdrawn colour';
const AMOUNT_ABOVE = "amount above the spent coin's value";
const NEGATIVE_SUB = 'result of subtraction would be negative';
const INSUFFICIENT = 'insufficient balance';

const S6 = ['frame', 'custody', 'witness'].some((x) => SECTIONS.includes(x));
const sig65 = (t: Eip712TypedData, w = wallet) => parseEvmSignature(w.signDigest(typedDataDigest(t)));
const authFor = (t: Eip712TypedData, counter = 0n, d = device, w = wallet) => {
  const p = sig65(t, w);
  return { pk: d.pk, use_counter: counter, blind: d.blind, sig: { r: p.r, s: p.s } };
};
const frameOf = (a: LocalAccount, d = device) => ({ account: a.addressBytes, device: d.address, authNonce: ledgerOf(a).auth_nonce as bigint });
const fill = (n: number, b: number) => new Uint8Array(n).fill(b);

// The activated account (device index 0) every S6E section starts from.
const S6_A0 = S6 ? (await execute(Original.Contract, await dormant(device.bootCommitment(salt), recoveryPk), ACTIVATE, device.activationArgs(salt))).after : undefined;

// Unshielded: two colours deposited locally (deposit_unshielded is upstream's
// permissionless circuit; local execution records the receive).
const COL_U = fill(32, 0xc1), COL_X = fill(32, 0xc2);
const RECIPIENT_U = fill(32, 0x77);
const depositedU = async () => {
  let a = S6_A0!;
  for (const c of [COL_U, COL_X]) a = (await execute(Original.Contract, a, 'deposit_unshielded', [c, 1000n])).after;
  return a;
};

// Shielded: an account whose local Zswap tree holds `coins` (in order) and
// whose held_coin witness answers `answer` for colour key `key`.
const COL_A = fill(32, 0xa1), COL_B = fill(32, 0xb2);
const NONCE_H = fill(32, 0x11), NONCE_OTHER = fill(32, 0x12), FILLER = (i: number) => fill(32, 0xf0 + i);
const shieldedAccount = (coins: { nonce: Uint8Array; color: Uint8Array; value: bigint }[], key: Uint8Array, pick: number) => {
  const { account, coins: placed } = withLocalCoins(S6_A0!, coins);
  return { a: { ...account, privateState: coinStoreAnswering([{ key, coin: placed[pick] }]) } as LocalAccount, coin: placed[pick] };
};
const RECIPIENT_CONTRACT = fill(32, 0x3c);
const shieldedMessage = (circuit: string, a: LocalAccount, amount: bigint, coin: { nonce: Uint8Array; value: bigint; mtIndex: bigint }, color = COL_A) =>
  circuit === WS
    ? evmEip712Messages.withdrawShielded(frameOf(a), color, amount, localCoinPublicKeyBytes(), coin)
    : evmEip712Messages.withdrawShieldedToContract(frameOf(a), color, amount, RECIPIENT_CONTRACT, coin);
const shieldedArgs = (circuit: string, amount: bigint, auth: unknown, color = COL_A) =>
  circuit === WS ? [{ bytes: localCoinPublicKeyBytes() }, color, amount, auth] : [{ bytes: RECIPIENT_CONTRACT }, color, amount, auth];

// ── G1E-1: the frame mutant ──────────────────────────────────────────────────
//
// The attacker holds the victim device's blind and counter (worst case) and
// its own key. The mutant's generated JavaScript derives the VICTIM's address
// from the attacker's point, so locally the victim's entry matches, the
// message names the victim's address, and the attacker's signature verifies
// against the attacker's point: no JavaScript check fails. The proof derives
// the address from the point itself, so the disclosed entry cannot be
// reproduced: refused at the proof server.
if (SECTIONS.includes('frame')) {
  const attacker = new SoftwareEvmWallet(0xbad5eedn);
  const forging = await loadPatched([], FORGE_ADDRESS_OVERRIDES);
  const A0 = S6_A0!;
  const AU = await depositedU();
  const victimAuth = (t: Eip712TypedData) => { const p = sig65(t, attacker); return { pk: attacker.pk, use_counter: 0n, blind: device.blind, sig: { r: p.r, s: p.s } }; };
  const fired = () => (forgery.fired > 0 ? undefined : 'the forgery never fired (the mutant missed its target)');
  const k = fill(32, 0x6b), e = rnd(192);
  // [label, account, circuit, message, args(auth)]: each case's honest call
  // (the device's own signature) is the copy's positive control, proved
  // through the forging copy with the forgery armed (it fires only for the
  // attacker's point, so the honest call is untouched)
  const cases: [string, LocalAccount, string, Eip712TypedData, (auth: unknown) => unknown[]][] = [
    ['rotate_enc_key', A0, ROTATE, evmEip712Messages.rotateEncKey(frameOf(A0), k), (au) => [k, au]],
    ['append_inbox', A0, APPEND, evmEip712Messages.appendInbox(frameOf(A0), e), (au) => [e, au]],
    ['withdraw_unshielded', AU, WU, evmEip712Messages.withdrawUnshielded(frameOf(AU), COL_U, 10n, RECIPIENT_U), (au) => [COL_U, 10n, { bytes: RECIPIENT_U }, au]],
  ];
  for (const circuit of [WS, WSC]) {
    const { a, coin } = shieldedAccount([{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }], COL_A, 1);
    cases.push([circuit.replace('_with_evm_eip712', ''), a, circuit, shieldedMessage(circuit, a, 300n, coin), (au) => shieldedArgs(circuit, 300n, au)]);
  }
  for (const [label, a, circuit, td, args] of cases) {
    // the message names the victim's address (what the forged derivation yields)
    forgery.set({ pk: attacker.pk, address: device.address });
    await negative('frame', `${label}: the attacker's key with the victim's address forged into the derivation`, a, circuit, args(victimAuth(td)),
      UNKNOWN, [], '', { module: forging, mutant: 'forged-address mutant (keccak256 override: the copy derives the victim address from the attacker point)',
        check: fired, control: { a, args: args(authFor(td)) } });
  }
  forgery.set(undefined);
}

// ── S6E: append_inbox and withdraw_unshielded ───────────────────────────────
if (SECTIONS.includes('custody')) {
  const A0 = S6_A0!;
  const posPath = await loadPatched([INVALID, UNKNOWN, INSUFFICIENT]);
  // append_inbox
  const E1 = rnd(192), E2 = rnd(192);
  const tdE = evmEip712Messages.appendInbox(frameOf(A0), E1);
  await positive('custody', 'append_inbox: honest (patched path)', posPath, A0, APPEND, [E1, authFor(tdE)]);
  await negative('custody', 'append_inbox binding: entry signed E2, executed E1', A0, APPEND, [E1, authFor(evmEip712Messages.appendInbox(frameOf(A0), E2))], INVALID, [INVALID]);
  const E1b = new Uint8Array(E1); E1b[191] ^= 1;
  await negative('custody', 'append_inbox binding: the last ciphertext byte flipped', A0, APPEND, [E1b, authFor(tdE)], INVALID, [INVALID]);
  await negative('custody', 'append_inbox replay/operation: a RotateEncKey signature', A0, APPEND,
    [E1, authFor(evmEip712Messages.rotateEncKey(frameOf(A0), E1.subarray(0, 32)))], INVALID, [INVALID]);
  // withdraw_unshielded (mirror: 1000 of COL_U and of COL_X)
  const AU = await depositedU();
  const tdU = evmEip712Messages.withdrawUnshielded(frameOf(AU), COL_U, 400n, RECIPIENT_U);
  await positive('custody', 'withdraw_unshielded: honest 400 of 1000 (patched path)', posPath, AU, WU, [COL_U, 400n, { bytes: RECIPIENT_U }, authFor(tdU)]);
  await positive('custody', 'withdraw_unshielded: the whole mirror, 1000 (patched path)', posPath, AU, WU,
    [COL_U, 1000n, { bytes: RECIPIENT_U }, authFor(evmEip712Messages.withdrawUnshielded(frameOf(AU), COL_U, 1000n, RECIPIENT_U))]);
  await negative('custody', 'withdraw_unshielded binding: amount signed 400, executed 401', AU, WU, [COL_U, 401n, { bytes: RECIPIENT_U }, authFor(tdU)], INVALID, [INVALID]);
  await negative('custody', 'withdraw_unshielded binding: colour signed U, executed X', AU, WU, [COL_X, 400n, { bytes: RECIPIENT_U }, authFor(tdU)], INVALID, [INVALID]);
  await negative('custody', 'withdraw_unshielded binding: another recipient', AU, WU, [COL_U, 400n, { bytes: fill(32, 0x78) }, authFor(tdU)], INVALID, [INVALID]);
  await runtimeOnly('custody', 'withdraw_unshielded: over-withdrawal (1001 of a 1000 mirror), honestly signed', AU, WU,
    [COL_U, 1001n, { bytes: RECIPIENT_U }, authFor(evmEip712Messages.withdrawUnshielded(frameOf(AU), COL_U, 1001n, RECIPIENT_U))], INSUFFICIENT,
    "upstream's shared chip (debit_unshielded); with its assert and the checked subtraction bypassed, the generated JavaScript's type encoder refuses the negative balance ('expected UnsignedInteger'), which is not an assert; in-circuit, the assert and the subtraction's range check refuse it");
  await negative('custody', 'withdraw_unshielded replay/operation: an AppendInbox signature', AU, WU, [COL_U, 400n, { bytes: RECIPIENT_U }, authFor(tdE)], INVALID, [INVALID]);
}

// ── S6E: witness substitution on the shielded spends ────────────────────────
//
// The honest coin H = (NONCE_H, COL_A, 1000) sits at Merkle index 1 (a filler
// coin at 0). Each negative signs a valid message over H, then the local
// tree holds a DIFFERENT coin where the substituted witness says it is, so
// the Zswap spend of the substituted coin is valid and only the arm
// circuit can refuse it.
if (SECTIONS.includes('witness')) {
  for (const circuit of [WS, WSC]) {
    const tag = circuit === WS ? 'withdraw_shielded' : 'withdraw_shielded_to_contract';
    const posPath = await loadPatched([INVALID, COLOUR, AMOUNT_ABOVE, NEGATIVE_SUB]);
    const honestTree = [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }];
    const H = shieldedAccount(honestTree, COL_A, 1);
    const tdH = shieldedMessage(circuit, H.a, 300n, H.coin);
    const authH = authFor(tdH);
    await positive('witness', `${tag}: honest partial spend 300 of 1000 (change 700, patched path)`, posPath, H.a, circuit, shieldedArgs(circuit, 300n, authH));
    await positive('witness', `${tag}: honest full spend 1000 (no change)`, posPath, H.a, circuit,
      shieldedArgs(circuit, 1000n, authFor(shieldedMessage(circuit, H.a, 1000n, H.coin))));
    // colour: the witness coin is (NONCE_H, COL_B, 1000) at index 1; the
    // signature over colour A still verifies (colour is shown once, as the
    // argument), so only the FR-010 assert refuses
    const colour = shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_B, value: 1000n }], COL_A, 1);
    await negative('witness', `${tag}: valid signature for colour A, witness coin of colour B (same nonce, value, index)`, colour.a, circuit,
      shieldedArgs(circuit, 300n, authH), COLOUR, [COLOUR]);
    // value: the witness coin is (NONCE_H, COL_A, 999) at index 1
    const value = shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_A, value: 999n }], COL_A, 1);
    await negative('witness', `${tag}: valid signature for coin value 1000, witness coin of value 999`, value.a, circuit,
      shieldedArgs(circuit, 300n, authH), INVALID, [INVALID]);
    // nonce: the witness coin is (NONCE_OTHER, COL_A, 1000) at index 1
    const nonce = shieldedAccount([honestTree[0], { nonce: NONCE_OTHER, color: COL_A, value: 1000n }], COL_A, 1);
    await negative('witness', `${tag}: valid signature for coin nonce N, witness coin of nonce N'`, nonce.a, circuit,
      shieldedArgs(circuit, 300n, authH), INVALID, [INVALID]);
    // index: H sits at index 2 (another coin at 1); the signature says index 1
    const index = shieldedAccount([honestTree[0], { nonce: FILLER(1), color: COL_A, value: 7n }, honestTree[1]], COL_A, 2);
    await negative('witness', `${tag}: valid signature for Merkle index 1, witness coin at index 2`, index.a, circuit,
      shieldedArgs(circuit, 300n, authH), INVALID, [INVALID]);
    // amount above the coin's value: a witness coin of value 200 against a
    // signed amount of 300 (the client refuses to build such a message)
    const small = shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_A, value: 200n }], COL_A, 1);
    await runtimeOnly('witness', `${tag}: witness coin of value 200 below the signed amount 300`, small.a, circuit,
      shieldedArgs(circuit, 300n, authH), AMOUNT_ABOVE,
      "with the arm's assert and the checked subtraction bypassed, the generated JavaScript's type encoder refuses the negative change ('expected UnsignedInteger'), which is not an assert; in-circuit, the assert, the subtraction's range check and the signature over the shown value refuse it");
  }
}

const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  const suffix = process.argv.slice(2).length ? `-${process.argv.slice(2).join('-')}` : '';
  const file = path.join(process.env.EVIDENCE_DIR, `evm-eip712-prover${suffix}.json`);
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify({ suite: 'evm-eip712-prover', sections: SECTIONS, ranAt: new Date().toISOString(), proofServer: CONFIG.proofServer,
    device: { address: device.checksumAddress }, cases: results, requests: proofLog.length, transportRetries, verdict,
  }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ evm-eip712-prover [${SECTIONS.join(', ')}]: ${verdict} (${results.length} cases; ${failures} FAIL, ${errors} ERROR; ${proofLog.length} proof-server requests)`);
process.exit(verdict === 'PASS' ? 0 : 1);
