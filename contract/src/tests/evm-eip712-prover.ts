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
//   devices     (S7E) add_device and remove_device with readable descriptors:
//               every target scheme enrolled at the current epoch and
//               counter 0, its entry equal to the target scheme's own
//               derivation; binding of each descriptor field and of the
//               scheme; an unregistered tag (or another recipe's tag) refused
//               at the constraint level under a valid signature (the FR-005
//               tightening); removal by descriptor and by literal entry (Q20),
//               the form swap, S13 in both forms, the last device, an entry
//               planted at device_epoch + 1 by an upstream arm evicted by
//               descriptor at that epoch;
//   grants      (S8E) issue_grant (k256, evm_eip712 and passkey grantees),
//               revoke_grant, revoke_all_grants and the grantee twins:
//               binding of scope fields, the caller pin, the grantee's
//               descriptor and the labelled origin hash (Q17); the arm's
//               issue rules (a read key only with read, an RP hash only for
//               a passkey) under a valid signature; the grantee twins'
//               binding, the stale grant nonce, the grant seam's forged
//               address (G1E-1), a wrong blind, and the shielded twins'
//               witness substitution (colour, value);
//   recovery    (S9E) publish_recovery_session_with_evm_eip712 and
//               recover_cancel_with_evm_eip712: positives (a session, a cancel
//               of a pending recovery, a fresh device's session after a
//               finalised recovery); the binding of every signed member of
//               PublishRecoverySession (the effect line, the key, the session
//               identifier, each phi, the length, the wrap, the nonce, the
//               type); every assert of the shared chips reached through the
//               arm under a VALID signature (pending, the phi length and
//               slots, the session identifier, the commitment, the identity
//               key; nothing to cancel); the seam's asserts on both circuits
//               (an unenrolled key, r = 0); and, after a finalised recovery,
//               the old evm_eip712 devices and an entry planted at
//               device_epoch + 1 before it (#183 clears the set);
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
import { JubjubDevice, K256Device, k256Challenges, jubjubChallenges, authArgs } from '../wallet/signer.js';
import { recoveryKey, signRecoverSubmit, recoverSubmitArgs, recoverSubmitChallenge, JUBJUB_IDENTITY, JUBJUB_ORDER_TWO } from '../wallet/recovery-gate.js';
import { SoftwareEvmWallet, EvmEip712Device, EvmEip712Grantee, highSTwin, parseEvmSignature, serialiseEvmSignature, evmEip712DescriptorInput, evmDeviceDescriptor, EVM_EIP712_UNUSED_DESCRIPTOR, evmEip712GranteeInput, evmEip712IssueArgs } from '../wallet/signer-evm-eip712.js';
import { grantLabel, grantOriginHash } from '../wallet/descriptors.js';
import { K256Grantee, originHash as upstreamOriginHash, grantAuthArgs, RECIPIENT_USER_ADDRESS, type GrantOpening } from '../wallet/signer.js';
import type { IssueScope } from '../wallet/evm-eip712-codec.js';
import { DESCRIPTOR_TAGS, padTag, type Descriptor } from '../wallet/descriptors.js';
import { softwarePasskey } from './p256-fixtures.js';
import { ed25519 } from '@noble/curves/ed25519.js';
import { evmEip712Messages, typedDataDigest, type Eip712TypedData } from '../wallet/evm-eip712-codec.js';
import { expectRefusal, expectSuccess, type NegativeResult, type PositiveResult } from './constraint-negative.js';
import {
  Original, loadPatched, dormant, execute, prove, ledgerOf, proofLog, forgery, withLocalCoins, coinStoreAnswering,
  localCoinPublicKeyBytes, transportRetries, FORGE_ADDRESS_OVERRIDES, POINT_AT_INFINITY_OVERRIDES, NON_CANONICAL_COORDINATE_OVERRIDES, type LocalAccount, type LocalCoin,
} from './evm-eip712-negative.js';
import type { BypassedContractModule } from './constraint-negative.js';

const SECTIONS = process.argv.slice(2).length ? process.argv.slice(2) : ['activation', 'reactivation', 'qa1', 'seam', 'frame', 'custody', 'witness', 'devices', 'grants', 'recovery'];
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

// ═════════════════════════════════════════════════════════════════════════════
// S7E: device lifecycle with readable descriptors
// ═════════════════════════════════════════════════════════════════════════════

if (SECTIONS.includes('devices')) {
  const ADD = 'add_device_with_evm_eip712';
  const REMOVE = 'remove_device_with_evm_eip712';
  const NOT_DEVICE_TAG = 'evm_eip712: not a registered device tag';
  const W117 = 'descriptor: not a 117-byte device tag';
  const LAST = 'cannot remove last device';
  const SELF = 'cannot remove the authorising device';
  const NONCANON = 'noncanonical absent entry';
  const A0 = (await execute(Original.Contract, await dormant(device.bootCommitment(salt), recoveryPk), ACTIVATE, device.activationArgs(salt))).after;
  const frame = (a: LocalAccount) => ({ account: a.addressBytes, device: device.address, authNonce: ledgerOf(a).auth_nonce as bigint });
  const signAs = (t: Eip712TypedData, counter: bigint) => { const p = parseEvmSignature(wallet.signDigest(typedDataDigest(t))); return { pk: device.pk, use_counter: counter, blind: device.blind, sig: { r: p.r, s: p.s } }; };
  const counterOf = (a: LocalAccount) => { for (let k = 0n; k < 64n; k++) if (ledgerOf(a).devices.member(device.entryAt(a.addressBytes, ledgerOf(a).device_epoch, k))) return k; throw new Error('device not live'); };
  const NONE = { is_some: false, value: new Uint8Array(32) };
  // targets, one per scheme
  const jub = JubjubDevice.generate();
  const k1 = new K256Device(0x5eed1n);
  const pass = softwarePasskey();
  const evm2 = await EvmEip712Device.enrol(new SoftwareEvmWallet(0xe2n), 'undeployed', 0);
  const solSk = new Uint8Array(32).fill(0x51);
  const solKey = ed25519.getPublicKey(solSk);
  const targets: [string, Descriptor, (acc: LocalAccount, epoch: bigint) => Uint8Array][] = [
    ['jubjub', { scheme: 'jubjub', x: jub.pk.x, y: jub.pk.y }, (acc, ep) => jub.entryAt(acc.addressBytes, ep, 0n)],
    ['k256', { scheme: 'k256', x: k1.pk.x, y: k1.pk.y, envelope: 0 }, (acc, ep) => k1.entryAt(acc.addressBytes, ep, 0n)],
    ['p256', { scheme: 'p256', x: pass.pk.x, y: pass.pk.y, policy: { rpIdHash: pass.policy.rp_id_hash, origin: pass.policy.origin } }, (acc, ep) => pass.device.entryAt(acc.addressBytes, ep, 0n)],
    ['evm_eip712', evmDeviceDescriptor(evm2), (acc, ep) => evm2.entryAt(acc.addressBytes, ep, 0n)],
    ['sol_ed25519', { scheme: 'sol_ed25519', key: solKey, blind: rnd(32) }, () => new Uint8Array(0)],
  ];
  const posPath = await loadPatched([INVALID, UNKNOWN, NOT_DEVICE_TAG, W117, SELF, LAST, NONCANON]);
  // add_device: every target scheme; the enrolled entry is the target
  // scheme's own derivation (upstream's derive_device_entry_with_<arm> for
  // jubjub, k256 and p256; the descriptor recipe for the new arms) at the
  // current epoch and counter 0
  for (const [scheme, d, upstreamEntry] of targets) {
    const input = evmEip712DescriptorInput(d);
    const td = evmEip712Messages.addDevice(frame(A0), input);
    const args = [input, signAs(td, 0n)];
    await positive('devices', `add_device: a ${scheme} target (patched path)`, posPath, A0, ADD, args);
    const after = (await execute(Original.Contract, A0, ADD, args)).after;
    const l = ledgerOf(after);
    const expected = scheme === 'sol_ed25519'
      ? pc.derive_descriptor_entry_w64(padTag(DESCRIPTOR_TAGS.device.sol_ed25519), { bytes: A0.addressBytes }, input.key, input.key2, 0n, 0n)
      : upstreamEntry(A0, 0n);
    const ok = l.devices.member(expected) && l.device_count === 2n && !l.devices.member(scheme === 'sol_ed25519' ? new Uint8Array(32) : upstreamEntry(A0, 1n));
    const r: Result = { section: 'devices', circuit: ADD, case: `add_device: the ${scheme} entry equals ${scheme === 'sol_ed25519' ? 'the descriptor recipe' : `upstream's derive_device_entry_with_${scheme}`} at epoch 0, counter 0; nothing at epoch 1`, kind: 'positive' };
    r.positive = { name: r.case, verdict: ok ? 'PASS' : 'FAIL', reason: ok ? 'state checked' : 'entry missing or wrong', proofServer: [], startedAt: new Date().toISOString(), ms: 0 };
    tally(r.positive); results.push(r); line(r);
  }
  // binding of descriptor fields and of the scheme
  const kIn = evmEip712DescriptorInput(targets[1][1]);
  const kTd = evmEip712Messages.addDevice(frame(A0), kIn);
  const flip = (b: Uint8Array) => { const c = new Uint8Array(b); c[0] ^= 1; return c; };
  await negative('devices', 'add_device binding: k256 x changed after signing', A0, ADD, [{ ...kIn, key: flip(kIn.key) }, signAs(kTd, 0n)], INVALID, [INVALID]);
  await negative('devices', 'add_device binding: k256 envelope changed after signing', A0, ADD, [{ ...kIn, envelope: 1n }, signAs(kTd, 0n)], INVALID, [INVALID]);
  const pIn = evmEip712DescriptorInput(targets[2][1]);
  const pTd = evmEip712Messages.addDevice(frame(A0), pIn);
  const o2 = new Uint8Array(pIn.origin); o2[20] = 0x39;
  await negative('devices', 'add_device binding: passkey origin changed after signing', A0, ADD, [{ ...pIn, origin: o2 }, signAs(pTd, 0n)], INVALID, [INVALID]);
  await negative('devices', 'add_device binding: passkey RP hash changed after signing', A0, ADD, [{ ...pIn, rp_id_hash: flip(pIn.rp_id_hash) }, signAs(pTd, 0n)], INVALID, [INVALID]);
  const eIn = evmEip712DescriptorInput(targets[3][1]);
  const eTd = evmEip712Messages.addDevice(frame(A0), eIn);
  await negative('devices', 'add_device binding: EVM target privacy salt changed after signing', A0, ADD, [{ ...eIn, key2: flip(eIn.key2) }, signAs(eTd, 0n)], INVALID, [INVALID]);
  await negative('devices', 'add_device binding: EVM target address changed after signing', A0, ADD, [{ ...eIn, address: flip(eIn.address) }, signAs(eTd, 0n)], INVALID, [INVALID]);
  // the circuit-fixed consequence line (FR-023): a message whose effect line
  // says something else is not this circuit's message
  const softer = JSON.parse(JSON.stringify(kTd)); softer.message.effect = 'Adds a helper key';
  await negative('devices', 'add_device: the effect line changed in the signed message', A0, ADD, [kIn, signAs(softer, 0n)], INVALID, [INVALID]);
  const jIn = evmEip712DescriptorInput(targets[0][1]);
  await negative('devices', 'add_device binding: a JubjubDevice signature executed under the Solana tag (same 64 payload bytes)', A0, ADD,
    [{ ...jIn, tag: padTag(DESCRIPTOR_TAGS.device.sol_ed25519) }, signAs(evmEip712Messages.addDevice(frame(A0), jIn), 0n)], INVALID, [INVALID]);
  // unregistered tag under a VALID signature: the passkey branch's struct hash
  // names the scheme by its constant, not by the tag bytes, so a signature
  // over a PasskeyDevice message verifies; only the tag checks refuse
  for (const [label, tag] of [['an unregistered tag', padTag('midnight:account:device:zz:v9')], ["another recipe's tag (k256 boot)", padTag(DESCRIPTOR_TAGS.boot.k256)]] as const) {
    await negative('devices', `add_device: ${label}, valid signature over the passkey fields`, A0, ADD,
      [{ ...pIn, tag }, signAs(pTd, 0n)], NOT_DEVICE_TAG, [NOT_DEVICE_TAG, W117]);
  }
  // remove_device: an account with the device D and a k256 device K
  const AK = (await execute(Original.Contract, A0, ADD, [kIn, signAs(kTd, 0n)])).after; // D now at counter 1
  const kEntry = k1.entryAt(AK.addressBytes, 0n, 0n);
  const remTd = (a: LocalAccount, input: typeof kIn, ep: bigint, ctr: bigint) => evmEip712Messages.removeDevice(frame(a), input, ep, ctr);
  await positive('devices', 'remove_device: the k256 device by descriptor (epoch 0, counter 0)', posPath, AK, REMOVE,
    [kIn, 0n, 0n, NONE, signAs(remTd(AK, kIn, 0n, 0n), 1n)]);
  await positive('devices', 'remove_device: the k256 entry by the literal form (Q20)', posPath, AK, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: kEntry }, signAs(evmEip712Messages.removeUnknownDevice(frame(AK), kEntry), 1n)]);
  await negative('devices', 'remove_device binding: targetCounter signed 0, executed 1', AK, REMOVE, [kIn, 0n, 1n, NONE, signAs(remTd(AK, kIn, 0n, 0n), 1n)], INVALID, [INVALID, UNKNOWN]);
  await negative('devices', 'remove_device binding: the literal entry changed after signing', AK, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: flip(kEntry) }, signAs(evmEip712Messages.removeUnknownDevice(frame(AK), kEntry), 1n)], INVALID, [INVALID, UNKNOWN]);
  await negative('devices', 'remove_device form swap: a RemoveUnknownDevice signature executed in the descriptor form', AK, REMOVE,
    [kIn, 0n, 0n, NONE, signAs(evmEip712Messages.removeUnknownDevice(frame(AK), kEntry), 1n)], INVALID, [INVALID]);
  await negative('devices', 'remove_device form swap: a RemoveDevice signature executed in the literal form', AK, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: kEntry }, signAs(remTd(AK, kIn, 0n, 0n), 1n)], INVALID, [INVALID]);
  const unkTd = JSON.parse(JSON.stringify(evmEip712Messages.removeUnknownDevice(frame(AK), kEntry))); unkTd.message.effect = 'Removes a device';
  await negative('devices', 'remove_device (Q20): the fixed revocation line changed in the signed message', AK, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: kEntry }, signAs(unkTd, 1n)], INVALID, [INVALID]);
  await negative('devices', 'remove_device: a non-canonical absent literal entry', AK, REMOVE,
    [kIn, 0n, 0n, { is_some: false, value: kEntry }, signAs(remTd(AK, kIn, 0n, 0n), 1n)], NONCANON, [NONCANON]);
  // S13: the caller's own post-roll entry (D at counter 1 rolls to 2)
  const self = evmEip712DescriptorInput(evmDeviceDescriptor(device));
  const selfPost = device.entryAt(AK.addressBytes, 0n, 2n);
  await negative('devices', 'S13: the device removes its own post-roll entry by descriptor', AK, REMOVE,
    [self, 0n, 2n, NONE, signAs(remTd(AK, self, 0n, 2n), 1n)], SELF, [SELF]);
  await negative('devices', 'S13: the device removes its own post-roll entry by the literal form', AK, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: selfPost }, signAs(evmEip712Messages.removeUnknownDevice(frame(AK), selfPost), 1n)], SELF, [SELF]);
  // the last device: only D (A0); a literal entry of nothing
  await negative('devices', 'the last device cannot be removed (account with one device)', A0, REMOVE,
    [EVM_EIP712_UNUSED_DESCRIPTOR, 0n, 0n, { is_some: true, value: device.entryAt(A0.addressBytes, 0n, 1n) },
     signAs(evmEip712Messages.removeUnknownDevice(frame(A0), device.entryAt(A0.addressBytes, 0n, 1n)), 0n)], LAST, [LAST, SELF]);
  // the future-epoch plant (README erratum 7): K (an upstream arm) enrols a
  // raw entry derived at device_epoch + 1; D evicts it by descriptor at
  // that epoch. add_device_with_evm_eip712 itself takes no epoch.
  const W = await EvmEip712Device.enrol(new SoftwareEvmWallet(0x3a37n), 'undeployed', 0);
  const plant = W.entryAt(AK.addressBytes, 1n, 0n);
  const kAuth = k1.sign(k256Challenges.addDevice({ contractAddress: AK.addressBytes, authNonce: ledgerOf(AK).auth_nonce }, k1.pk, plant), 0n);
  const AP = (await execute(Original.Contract, AK, 'add_device_with_k256', [plant, kAuth.pk, 0n, kAuth.sig, 0n])).after;
  const planted: Result = { section: 'devices', circuit: 'add_device_with_k256', case: 'the upstream residual: a k256 device plants an evm_eip712 entry at device_epoch + 1 (raw entry)', kind: 'positive' };
  const plantedOk = ledgerOf(AP).devices.member(plant) && ledgerOf(AP).device_count === 3n;
  planted.positive = { name: planted.case, verdict: plantedOk ? 'PASS' : 'FAIL', reason: plantedOk ? 'the planted entry is in the set (simulator)' : 'not planted', proofServer: [], startedAt: new Date().toISOString(), ms: 0 };
  tally(planted.positive); results.push(planted); line(planted);
  const wIn = evmEip712DescriptorInput(evmDeviceDescriptor(W));
  await positive('devices', 'remove_device: the planted entry evicted by descriptor at target epoch 1 (= device_epoch + 1)', posPath, AP, REMOVE,
    [wIn, 1n, 0n, NONE, signAs(remTd(AP, wIn, 1n, 0n), counterOf(AP))]);
}

// ═════════════════════════════════════════════════════════════════════════════
// S8E: grants
// ═════════════════════════════════════════════════════════════════════════════

if (SECTIONS.includes('grants')) {
  const ISSUE = 'issue_grant_with_evm_eip712', REVOKE = 'revoke_grant_with_evm_eip712', REVOKE_ALL = 'revoke_all_grants_with_evm_eip712';
  const GWU = 'withdraw_unshielded_with_grant_evm_eip712', GWS = 'withdraw_shielded_with_grant_evm_eip712';
  const READ_KEY = 'evm_eip712: a read key without read';
  const RP_ONLY = 'evm_eip712: an RP hash belongs to a passkey grantee';
  const GINVALID = 'invalid grant signature';
  const UNKNOWN_GRANT = 'unknown grant';
  const COLOUR_G = 'held coin colour does not match the withdrawn colour';
  const A0 = (await execute(Original.Contract, await dormant(device.bootCommitment(salt), recoveryPk), ACTIVATE, device.activationArgs(salt))).after;
  const frame = (a: LocalAccount) => ({ account: a.addressBytes, device: device.address, authNonce: ledgerOf(a).auth_nonce as bigint });
  const signAs = (t: Eip712TypedData, counter: bigint) => { const p = parseEvmSignature(wallet.signDigest(typedDataDigest(t))); return { pk: device.pk, use_counter: counter, blind: device.blind, sig: { r: p.r, s: p.s } }; };
  const counterOf = (a: LocalAccount) => { for (let k = 0n; k < 64n; k++) if (ledgerOf(a).devices.member(device.entryAt(a.addressBytes, ledgerOf(a).device_epoch, k))) return k; throw new Error('device not live'); };
  const scopeOf = (o: Partial<IssueScope>): IssueScope => ({ opWithdrawUnshielded: false, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: false,
    color: new Uint8Array(32), recipientKind: 0n, recipient: new Uint8Array(32), maxCoinValue: 0n, perCallCap: 0n, cap: 0n, expiresAt: 0n,
    rpIdHash: new Uint8Array(32), readPk: new Uint8Array(32), windowLen: 0n, windowCap: 0n, caller: null, ...o });
  const issueArgs = (a: LocalAccount, gin: any, sc: IssueScope, sSalt: Uint8Array, signed: IssueScope = sc, rawReadPk?: Uint8Array) => {
    const args = evmEip712IssueArgs(sc, sSalt);
    if (rawReadPk) args[12] = rawReadPk;
    return [gin, ...args, signAs(evmEip712Messages.issueGrant(frame(a), gin, signed), counterOf(a))];
  };
  // grantees
  const label = grantLabel('bank.example');
  const gWallet = new SoftwareEvmWallet(0x6a17een);
  const eg = await EvmEip712Grantee.enrol(gWallet, 'undeployed', 0, label, 0n);
  const kg = K256Grantee.generate();
  const kOrigin = upstreamOriginHash('https://bank.example');
  const pass = softwarePasskey();
  const egIn = eg.descriptor();
  const kgIn = evmEip712GranteeInput({ scheme: 'k256', x: kg.pk.x, y: kg.pk.y, envelope: 0 }, { originHash: kOrigin }, 0n);
  const pgIn = evmEip712GranteeInput({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y }, { origin: pass.policy.origin }, 0n);
  const COL = fill(32, 0xc7), RCPT = fill(32, 0x7e);
  const unsh = scopeOf({ opWithdrawUnshielded: true, color: COL, cap: 450n, perCallCap: 300n, maxCoinValue: 300n, recipientKind: RECIPIENT_USER_ADDRESS, recipient: RCPT });
  const sSalt = fill(32, 0x5a);
  const posPath = await loadPatched([INVALID, UNKNOWN, READ_KEY, RP_ONLY, GINVALID, UNKNOWN_GRANT, COLOUR_G]);

  // issue_grant positives: an evm_eip712, a k256 and a passkey grantee (with its RP)
  await positive('grants', 'issue_grant: an evm_eip712 grantee, unshielded scope (patched path)', posPath, A0, ISSUE, issueArgs(A0, egIn, unsh, sSalt));
  await positive('grants', 'issue_grant: a k256 grantee (labelled origin hash, Q17), pinned caller', posPath, A0, ISSUE, issueArgs(A0, kgIn, { ...unsh, caller: fill(32, 0xca) }, sSalt));
  const rd = fill(32, 0x9d);
  await positive('grants', 'issue_grant: a passkey grantee with its RP hash, read-only', posPath, A0, ISSUE,
    issueArgs(A0, pgIn, scopeOf({ read: true, readPk: rd, rpIdHash: pass.policy.rp_id_hash }), sSalt));
  // binding: a scope field, the caller pin, the grantee descriptor, Q17's label
  const signedUnsh = issueArgs(A0, egIn, unsh, sSalt);
  await negative('grants', 'issue_grant binding: cap signed 450, executed 451', A0, ISSUE, [egIn, ...evmEip712IssueArgs({ ...unsh, cap: 451n }, sSalt), signedUnsh.at(-1)], INVALID, [INVALID]);
  await negative('grants', 'issue_grant binding: a caller pin added after signing', A0, ISSUE, [egIn, ...evmEip712IssueArgs({ ...unsh, caller: fill(32, 0xca) }, sSalt), signedUnsh.at(-1)], INVALID, [INVALID]);
  await negative('grants', 'issue_grant binding: the grantee\'s site label changed after signing', A0, ISSUE, [{ ...egIn, label: grantLabel('evil.example') }, ...evmEip712IssueArgs(unsh, sSalt), signedUnsh.at(-1)], INVALID, [INVALID]);
  await negative('grants', 'issue_grant binding: the grantee slot changed after signing', A0, ISSUE, [{ ...egIn, slot: 1n }, ...evmEip712IssueArgs(unsh, sSalt), signedUnsh.at(-1)], INVALID, [INVALID]);
  const signedK = issueArgs(A0, kgIn, unsh, sSalt);
  await negative('grants', 'issue_grant binding: a k256 grantee\'s labelled origin hash changed after signing (Q17)', A0, ISSUE,
    [{ ...kgIn, origin_hash: upstreamOriginHash('https://evil.example') }, ...evmEip712IssueArgs(unsh, sSalt), signedK.at(-1)], INVALID, [INVALID]);
  const issueSoft = JSON.parse(JSON.stringify(evmEip712Messages.issueGrant(frame(A0), egIn, unsh))); issueSoft.message.effect = 'Lets this site read your balance';
  await negative('grants', 'issue_grant: the effect line changed in the signed message', A0, ISSUE, [egIn, ...evmEip712IssueArgs(unsh, sSalt), signAs(issueSoft, counterOf(A0))], INVALID, [INVALID]);
  // the arm's issue rules under a VALID signature
  await negative('grants', 'issue_grant: a read key without read (signed with readKey zero, executed with a key)', A0, ISSUE,
    issueArgs(A0, egIn, unsh, sSalt, unsh, fill(32, 0x11)), READ_KEY, [READ_KEY]);
  const rpScope = { ...unsh, rpIdHash: fill(32, 0x3f) };
  await negative('grants', 'issue_grant: an RP hash for a non-passkey grantee, honestly signed', A0, ISSUE, issueArgs(A0, egIn, rpScope, sSalt), RP_ONLY, [RP_ONLY]);
  // revoke_grant / revoke_all over an account holding the evm grant
  const AG = (await execute(Original.Contract, A0, ISSUE, issueArgs(A0, egIn, unsh, sSalt))).after;
  await positive('grants', 'revoke_grant: the evm_eip712 grantee by descriptor', posPath, AG, REVOKE, [egIn, signAs(evmEip712Messages.revokeGrant(frame(AG), egIn), counterOf(AG))]);
  // a second live grant (slot 1): the signed slot 0, the executed slot 1
  const eg1In = { ...egIn, slot: 1n };
  const AG2 = (await execute(Original.Contract, AG, ISSUE, issueArgs(AG, eg1In, unsh, sSalt))).after;
  await negative('grants', 'revoke_grant binding: signed for slot 0, executed for the live slot-1 grant', AG2, REVOKE,
    [eg1In, signAs(evmEip712Messages.revokeGrant(frame(AG2), egIn), counterOf(AG2))], INVALID, [INVALID]);
  await positive('grants', 'revoke_all_grants', posPath, AG, REVOKE_ALL, [signAs(evmEip712Messages.revokeAllGrants(frame(AG)), counterOf(AG))]);
  await negative('grants', 'revoke_all_grants replay/operation: a CancelRecovery signature (same bare frame)', AG, REVOKE_ALL,
    [signAs(evmEip712Messages.cancelRecovery(frame(AG)), counterOf(AG))], INVALID, [INVALID]);

  // the grantee twins
  const AU = (await execute(Original.Contract, AG, 'deposit_unshielded', [COL, 1000n])).after;
  const rec = (a: LocalAccount) => ledgerOf(a).grants.lookup(eg.grantId(a.addressBytes));
  const gframe = (a: LocalAccount, nonce?: bigint) => ({ account: a.addressBytes, grantee: eg.address, label, slot: 0n, issuedAt: rec(a).issued_at, grantNonce: nonce ?? rec(a).nonce });
  const opening: GrantOpening = { originHash: eg.originHash, slot: 0n, scopeSalt: sSalt, recipientKind: RECIPIENT_USER_ADDRESS, pinnedRecipient: RCPT, maxCoinValue: 300n, spentPrev: 0n };
  const gSign = (t: Eip712TypedData, w = gWallet, pk = eg.pk) => { const p = parseEvmSignature(w.signDigest(typedDataDigest(t))); return { arm: 'evm_eip712' as const, pk, blind: eg.blind, label, sig: { r: p.r, s: p.s } }; };
  const tdU = (a: LocalAccount, amt: bigint, nonce?: bigint) => evmEip712Messages.withdrawUnshieldedAsGrantee(gframe(a, nonce), COL, amt, RCPT);
  const twinArgs = (amt: bigint, auth: any, o: GrantOpening = opening) => [COL, amt, { bytes: RCPT }, ...grantAuthArgs(o, auth)];
  await positive('grants', 'withdraw_unshielded_with_grant: 200 by the evm_eip712 grantee (patched path)', posPath, AU, GWU, twinArgs(200n, gSign(tdU(AU, 200n))));
  // auth_nonce and every device entry untouched (simulator state check)
  const AU1 = (await execute(Original.Contract, AU, GWU, twinArgs(200n, gSign(tdU(AU, 200n))))).after;
  const untouched: Result = { section: 'grants', circuit: GWU, case: 'the grant call advanced only its record (nonce +1), never auth_nonce or a device entry (FR-008)', kind: 'positive' };
  const okU = ledgerOf(AU1).auth_nonce === ledgerOf(AU).auth_nonce && rec(AU1).nonce === rec(AU).nonce + 1n
    && [...ledgerOf(AU1).devices].map((d: Uint8Array) => Buffer.from(d).toString('hex')).sort().join() === [...ledgerOf(AU).devices].map((d: Uint8Array) => Buffer.from(d).toString('hex')).sort().join();
  untouched.positive = { name: untouched.case, verdict: okU ? 'PASS' : 'FAIL', reason: okU ? 'state checked' : 'auth_nonce or a device entry changed', proofServer: [], startedAt: new Date().toISOString(), ms: 0 };
  tally(untouched.positive); results.push(untouched); line(untouched);
  await negative('grants', 'grantee binding: amount signed 200, executed 201', AU, GWU, twinArgs(201n, gSign(tdU(AU, 200n))), GINVALID, [GINVALID]);
  await negative('grants', 'grantee replay: the approval of the first call after the record nonce advanced', AU1, GWU, twinArgs(200n, gSign(tdU(AU, 200n)), { ...opening, spentPrev: 200n }), GINVALID, [GINVALID]);
  await runtimeOnly('grants', 'grantee: another blind (a grant id with no record)', AU, GWU, twinArgs(200n, { ...gSign(tdU(AU, 200n)), blind: fill(32, 0x13) }), UNKNOWN_GRANT,
    "the blind is a ledger-pinned opening (not in the signed frame): another blind names a grant id with no record; with the membership assert bypassed the generated JavaScript's map lookup throws ('expected a cell'), which is not an assert; in-circuit the membership assert refuses it");
  await negative('grants', 'grantee replay/role: a device-role WithdrawUnshielded signature by the grantee key', AU, GWU,
    twinArgs(200n, gSign(evmEip712Messages.withdrawUnshielded({ account: AU.addressBytes, device: eg.address, authNonce: ledgerOf(AU).auth_nonce }, COL, 200n, RCPT))), GINVALID, [GINVALID]);
  // the grant seam's forged address (G1E-1): the attacker presents its own
  // point with the victim grantee's blind and label; the copy derives the
  // victim's address from it
  const forging = await loadPatched([], FORGE_ADDRESS_OVERRIDES);
  const attacker = new SoftwareEvmWallet(0xbad6n);
  forgery.set({ pk: attacker.pk, address: eg.address });
  await negative('grants', 'grant seam: the attacker\'s key with the grantee\'s address forged into the derivation', AU, GWU,
    twinArgs(200n, gSign(tdU(AU, 200n), attacker, attacker.pk)), UNKNOWN_GRANT, [], '',
    { module: forging, mutant: 'forged-address mutant (keccak256 override) on the grant seam', check: () => (forgery.fired > 0 ? undefined : 'the forgery never fired'),
      control: { a: AU, args: twinArgs(200n, gSign(tdU(AU, 200n))) } });
  forgery.set(undefined);
  // the shielded grantee twin on a local Zswap tree: a valid approval over
  // coin H, the witness answering another coin
  const shScope = scopeOf({ opWithdrawShielded: true, read: true, readPk: fill(32, 0x77), color: COL_A, cap: 2000n, perCallCap: 1000n, maxCoinValue: 1000n });
  const AS0 = (await execute(Original.Contract, A0, ISSUE, issueArgs(A0, egIn, shScope, sSalt))).after;
  const shOpening: GrantOpening = { originHash: eg.originHash, slot: 0n, scopeSalt: sSalt, recipientKind: 0n, pinnedRecipient: new Uint8Array(32), maxCoinValue: 1000n, spentPrev: 0n };
  const shAccount = (coins: { nonce: Uint8Array; color: Uint8Array; value: bigint }[], pick: number) => {
    const { account, coins: placed } = withLocalCoins(AS0, coins);
    return { a: { ...account, privateState: coinStoreAnswering([{ key: COL_A, coin: placed[pick] }]) } as LocalAccount, coin: placed[pick] };
  };
  const tree = [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }];
  const H = shAccount(tree, 1);
  const change = fill(192, 0x2c);
  const enc = ledgerOf(AS0).enc_key;
  const rS = (ledgerOf(AS0).grants.lookup(eg.grantId(AS0.addressBytes)));
  const tdS = evmEip712Messages.withdrawShieldedAsGrantee({ account: AS0.addressBytes, grantee: eg.address, label, slot: 0n, issuedAt: rS.issued_at, grantNonce: rS.nonce },
    COL_A, 300n, localCoinPublicKeyBytes(), change, enc, { nonce: NONCE_H, value: 1000n, mtIndex: H.coin.mtIndex });
  const sArgs = (auth: any) => [{ bytes: localCoinPublicKeyBytes() }, COL_A, 300n, change, enc, ...grantAuthArgs(shOpening, auth)];
  await positive('grants', 'withdraw_shielded_with_grant: 300 of a 1000 coin (change appended, patched path)', posPath, H.a, GWS, sArgs(gSign(tdS)));
  // the colour: upstream's scope check binds the SPENT coin's colour to the
  // grant's object commitment, so the FR-010 assert is isolated with a grant
  // whose scope colour is B: the grantee's valid approval names colour A, the
  // witness coin is B (admitted by the scope); only coin.color == color refuses
  const shScopeB = { ...shScope, color: COL_B };
  const ASB = (await execute(Original.Contract, A0, ISSUE, issueArgs(A0, egIn, shScopeB, sSalt))).after;
  const { account: treeB, coins: placedB } = withLocalCoins(ASB, [tree[0], { nonce: NONCE_H, color: COL_B, value: 1000n }]);
  const colourB = { ...treeB, privateState: coinStoreAnswering([{ key: COL_A, coin: placedB[1] }]) } as LocalAccount;
  const rB = ledgerOf(ASB).grants.lookup(eg.grantId(ASB.addressBytes));
  const tdSB = evmEip712Messages.withdrawShieldedAsGrantee({ account: ASB.addressBytes, grantee: eg.address, label, slot: 0n, issuedAt: rB.issued_at, grantNonce: rB.nonce },
    COL_A, 300n, localCoinPublicKeyBytes(), change, enc, { nonce: NONCE_H, value: 1000n, mtIndex: placedB[1].mtIndex });
  await negative('grants', 'grantee shielded: valid approval for colour A, witness coin of colour B (a grant scoped to B)', colourB, GWS, sArgs(gSign(tdSB)), COLOUR_G, [COLOUR_G]);
  const value999 = shAccount([tree[0], { nonce: NONCE_H, color: COL_A, value: 999n }], 1);
  await negative('grants', 'grantee shielded: valid approval for coin value 1000, witness coin of value 999', value999.a, GWS, sArgs(gSign(tdS)), GINVALID, [GINVALID]);
}

// ═════════════════════════════════════════════════════════════════════════════
// S9E: recovery — the session and the cancel through the arm
// ═════════════════════════════════════════════════════════════════════════════

if (SECTIONS.includes('recovery')) {
  const PUBLISH = 'publish_recovery_session_with_evm_eip712';
  const CANCEL = 'recover_cancel_with_evm_eip712';
  const PENDING = 'recovery pending; cancel first';
  const EMPTY = 'phi must not be empty';
  const RANGE = 'phi length out of range';
  const SLOT2 = 'unused phi slot 2 not zero', SLOT3 = 'unused phi slot 3 not zero', SLOT4 = 'unused phi slot 4 not zero';
  const SIDZERO = 'session nonce is zero', SIDREUSE = 'session nonce reused', PKREUSE = 'recovery commitment reused';
  const IDENT = 'recovery key is the identity', SMALL = 'recovery key has small order';
  const NOPENDING = 'no recovery pending';
  // The account's birth recovery key is one whose secret the test holds, so
  // that it can open the recovery gate (recover_submit) itself.
  const birth = 0xb1a7n;
  const field = (n: number) => BigInt('0x' + Buffer.from(rnd(31)).toString('hex')) + BigInt(n);
  type Sess = { recoveryPk: { x: bigint; y: bigint }; sessionNonce: Uint8Array; phi: [bigint, bigint, bigint, bigint]; phiLen: bigint; wrap: Uint8Array };
  const sessionOf = (secret: bigint): Sess => ({ recoveryPk: recoveryKey(secret).pk, sessionNonce: rnd(32), phi: [field(1), field(2), 0n, 0n], phiLen: 2n, wrap: rnd(64) });
  const sArgs = (x: Sess) => [x.recoveryPk, x.sessionNonce, ...x.phi, x.phiLen, x.wrap];
  const frame = (a: LocalAccount, d: EvmEip712Device = device) => ({ account: a.addressBytes, device: d.address, authNonce: ledgerOf(a).auth_nonce as bigint });
  const counterIn = (a: LocalAccount, d: EvmEip712Device) => { for (let k = 0n; k < 64n; k++) if (ledgerOf(a).devices.member(d.entryAt(a.addressBytes, ledgerOf(a).device_epoch, k))) return k; return 0n; };
  const signBy = async (d: EvmEip712Device, t: Eip712TypedData, counter: bigint) => { const { arm, ...auth } = await d.authorise(t, counter); return auth; };
  const pubArgs = async (a: LocalAccount, x: Sess, d: EvmEip712Device = device, signed?: (t: any) => void, counter = counterIn(a, d)) => {
    const td = evmEip712Messages.publishRecoverySession(frame(a, d), x);
    const t = signed ? JSON.parse(JSON.stringify(td)) : td;
    if (signed) signed(t);
    return [...sArgs(x), await signBy(d, t, counter)];
  };
  const cancelArgs = async (a: LocalAccount, d: EvmEip712Device = device, t?: Eip712TypedData, counter = counterIn(a, d)) =>
    [await signBy(d, t ?? evmEip712Messages.cancelRecovery(frame(a, d)), counter)];
  /** The shared JubJub gate: the recovery key `secret` and the successor co-sign. */
  const submitArgs = (a: LocalAccount, secret: bigint, successor: JubjubDevice, successorRecoveryPk: { x: bigint; y: bigint }, nowUpper: bigint) => {
    const l = ledgerOf(a);
    const auth = signRecoverSubmit(recoveryKey(secret), successor,
      recoverSubmitChallenge({ contractAddress: a.addressBytes, authNonce: l.auth_nonce }, l.recovery_pk, successor.pk, successorRecoveryPk as any, l.device_epoch + 1n, nowUpper),
      { successorRecoveryPk: successorRecoveryPk as any, expectedEpoch: l.device_epoch, expectedNonce: l.auth_nonce, nowUpper });
    return recoverSubmitArgs(auth);
  };
  const now = () => BigInt(Math.floor(Date.now() / 1000));
  const posPath = await loadPatched([INVALID, UNKNOWN, ZERO, PENDING, EMPTY, RANGE, SLOT2, SLOT3, SLOT4, SIDZERO, SIDREUSE, PKREUSE, IDENT, SMALL, NOPENDING]);

  // A0: the device, activated (counter 0); window 0 (the constructor's
  // minimum) so that a finalisation can run locally
  const A0 = (await execute(Original.Contract, await dormant(device.bootCommitment(salt), recoveryKey(birth).pk, 0n), ACTIVATE, device.activationArgs(salt))).after;
  const S1 = sessionOf(0x5e55n);
  await positive('recovery', 'publish_recovery_session: the honest session (patched path)', posPath, A0, PUBLISH, await pubArgs(A0, S1));
  const A1 = (await execute(Original.Contract, A0, PUBLISH, await pubArgs(A0, S1))).after; // device at counter 1, S1 stored
  if (ledgerOf(A1).recovery_phi_len !== 2n) throw new Error('setup: the session did not land');

  // binding: the signed message differs from the executed values in one member
  const S2 = sessionOf(0x5e56n);
  const otherKey = recoveryKey(0x0dd0n).pk;
  const hex32 = (v: bigint) => '0x' + Buffer.from(Array.from({ length: 32 }, (_, i) => Number((v >> BigInt(8 * i)) & 0xffn))).toString('hex');
  const flipHex = (h: string) => h.slice(0, -2) + (h.slice(-2) === '00' ? '01' : '00');
  const bindings: [string, (t: any) => void][] = [
    ['the effect line', (t) => { t.message.effect = 'Adds a backup'; }],
    ['recoveryKeyX', (t) => { t.message.recoveryKeyX = hex32(otherKey.x); }],
    ['recoveryKeyY', (t) => { t.message.recoveryKeyY = hex32(otherKey.y); }],
    ['sessionNonce', (t) => { t.message.sessionNonce = flipHex(t.message.sessionNonce); }],
    ['phi1', (t) => { t.message.phi1 = flipHex(t.message.phi1); }],
    ['phi2', (t) => { t.message.phi2 = flipHex(t.message.phi2); }],
    ['phi3 (signed non-zero, executed zero)', (t) => { t.message.phi3 = hex32(7n); }],
    ['phi4 (signed non-zero, executed zero)', (t) => { t.message.phi4 = hex32(7n); }],
    ['phiLength (signed 3, executed 2)', (t) => { t.message.phiLength = '3'; }],
    ['wrap (one byte)', (t) => { t.message.wrap = flipHex(t.message.wrap); }],
    ['authNonce (n + 1)', (t) => { t.message.authNonce = String(BigInt(t.message.authNonce) + 1n); }],
  ];
  for (const [name, f] of bindings) await negative('recovery', `publish binding: ${name} changed in the signed message`, A1, PUBLISH, await pubArgs(A1, S2, device, f), INVALID, [INVALID]);
  await negative('recovery', 'publish replay/operation: a CancelRecovery signature (bare frame) presented as the session approval', A1, PUBLISH,
    [...sArgs(S2), await signBy(device, evmEip712Messages.cancelRecovery(frame(A1)), 1n)], INVALID, [INVALID]);
  await negative('recovery', 'publish replay: the landed session approval replayed (entry consumed, nonce advanced, stored values)', A1, PUBLISH,
    await pubArgs(A0, S1, device, undefined, 0n), UNKNOWN, [UNKNOWN, INVALID, SIDREUSE, PKREUSE]);

  // the shared chip, through the arm, under a VALID signature
  const chip: [string, Sess, string, string[]][] = [
    ['an empty vector (length 0)', { ...S2, phi: [0n, 0n, 0n, 0n], phiLen: 0n }, EMPTY, [EMPTY]],
    ['a length beyond the slot bound (5)', { ...S2, phi: [1n, 2n, 3n, 4n], phiLen: 5n }, RANGE, [RANGE]],
    ['length 1 with phi2 non-zero', { ...S2, phi: [1n, 2n, 0n, 0n], phiLen: 1n }, SLOT2, [SLOT2]],
    ['length 2 with phi3 non-zero', { ...S2, phi: [1n, 2n, 3n, 0n], phiLen: 2n }, SLOT3, [SLOT3]],
    ['length 3 with phi4 non-zero', { ...S2, phi: [1n, 2n, 3n, 4n], phiLen: 3n }, SLOT4, [SLOT4]],
    ['an all-zero session identifier', { ...S2, sessionNonce: new Uint8Array(32) }, SIDZERO, [SIDZERO]],
    ['the stored session identifier reused', { ...S2, sessionNonce: new Uint8Array(S1.sessionNonce) }, SIDREUSE, [SIDREUSE]],
    ['the stored recovery commitment reused', { ...S2, recoveryPk: S1.recoveryPk }, PKREUSE, [PKREUSE]],
    ['the identity as the new recovery key', { ...S2, recoveryPk: JUBJUB_IDENTITY }, IDENT, [IDENT, SMALL]],
  ];
  for (const [name, x, expect, bypass] of chip) await negative('recovery', `publish under a valid signature: ${name}`, A1, PUBLISH, await pubArgs(A1, x), expect, bypass);
  await runtimeOnly('recovery', 'publish under a valid signature: a small-order recovery key', A1, PUBLISH, await pubArgs(A1, { ...S2, recoveryPk: JUBJUB_ORDER_TWO }), 'unreachable',
    'the runtime cannot construct a JubJub point outside the prime-order subgroup (it traps before the circuit body), and the proving toolchain constrains every assigned point into the subgroup (upstream recovery-sim, require_live_jubjub_point)');

  // the seam on the new circuits
  const stranger = await EvmEip712Device.enrol(other, 'undeployed', 0);
  await negative('recovery', 'publish: an unenrolled evm key signs the session', A1, PUBLISH, await pubArgs(A1, S2, stranger, undefined, 0n), UNKNOWN, [UNKNOWN]);
  await negative('recovery', 'publish: the device key with another blind', A1, PUBLISH,
    [...sArgs(S2), { ...(await signBy(device, evmEip712Messages.publishRecoverySession(frame(A1), S2), 1n)), blind: device1.blind }], UNKNOWN, [UNKNOWN]);
  await negative('recovery', 'publish: signature r = 0', A1, PUBLISH,
    [...sArgs(S2), { ...(await signBy(device, evmEip712Messages.publishRecoverySession(frame(A1), S2), 1n)), sig: { r: 0n, s: 5n } }], ZERO, [ZERO, INVALID]);

  // a pending recovery (AP): the device publishes, the gate opens with the
  // session's secret, a k256 device K and a jubjub device J are enrolled, and
  // J plants an evm_eip712 entry for W at device_epoch + 1 (erratum 7)
  const jub = JubjubDevice.generate();
  const jIn = evmEip712DescriptorInput({ scheme: 'jubjub', x: jub.pk.x, y: jub.pk.y });
  const AJ = (await execute(Original.Contract, A1, 'add_device_with_evm_eip712', [jIn, await signBy(device, evmEip712Messages.addDevice(frame(A1), jIn), 1n)])).after;
  const e2 = await EvmEip712Device.enrol(new SoftwareEvmWallet(0xe2e2n), 'undeployed', 0);
  const e2In = evmEip712DescriptorInput(evmDeviceDescriptor(e2));
  const AE = (await execute(Original.Contract, AJ, 'add_device_with_evm_eip712', [e2In, await signBy(device, evmEip712Messages.addDevice(frame(AJ), e2In), 2n)])).after;
  const W = await EvmEip712Device.enrol(new SoftwareEvmWallet(0x3a38n), 'undeployed', 0);
  const plant = W.entryAt(AE.addressBytes, 1n, 0n);
  const jPlant = jub.sign(jubjubChallenges.addDevice({ contractAddress: AE.addressBytes, authNonce: ledgerOf(AE).auth_nonce }, jub.pk, plant), 0n);
  const AW = (await execute(Original.Contract, AE, 'add_device_with_jubjub', [plant, ...authArgs(jPlant)])).after;
  if (!ledgerOf(AW).devices.member(plant)) throw new Error('setup: the plant did not land');
  const Q = JubjubDevice.generate();
  const QR = 0x9e11n;
  const AP = (await execute(Original.Contract, AW, 'recover_submit', submitArgs(AW, 0x5e55n, Q, recoveryKey(QR).pk, now() + 2n))).after;
  if (!ledgerOf(AP).pending_recovery) throw new Error('setup: the submission did not land');
  await negative('recovery', 'publish under a valid signature while a recovery is pending', AP, PUBLISH, await pubArgs(AP, S2), PENDING, [PENDING]);
  await positive('recovery', 'recover_cancel: the second evm device vetoes the pending recovery (patched path)', posPath, AP, CANCEL, await cancelArgs(AP, e2));
  await negative('recovery', 'cancel binding: a RevokeAllGrants signature over the same bare frame', AP, CANCEL, await cancelArgs(AP, e2, evmEip712Messages.revokeAllGrants(frame(AP, e2))), INVALID, [INVALID]);
  await negative('recovery', 'cancel binding: a CancelRecovery signature over authNonce + 1', AP, CANCEL,
    await cancelArgs(AP, e2, evmEip712Messages.cancelRecovery({ ...frame(AP, e2), authNonce: ledgerOf(AP).auth_nonce + 1n })), INVALID, [INVALID]);
  await negative('recovery', 'cancel binding: a CancelRecovery signature for another account', AP, CANCEL,
    await cancelArgs(AP, e2, evmEip712Messages.cancelRecovery({ ...frame(AP, e2), account: rnd(32) })), INVALID, [INVALID]);
  await negative('recovery', 'cancel: an unenrolled evm key', AP, CANCEL, await cancelArgs(AP, stranger, undefined, 0n), UNKNOWN, [UNKNOWN]);
  await negative('recovery', 'cancel: signature r = 0', AP, CANCEL, [{ ...(await cancelArgs(AP, e2))[0] as any, sig: { r: 0n, s: 5n } }], ZERO, [ZERO, INVALID]);
  await negative('recovery', 'cancel under a valid signature with nothing pending', A1, CANCEL, await cancelArgs(A1), NOPENDING, [NOPENDING]);
  const AC = (await execute(Original.Contract, AP, CANCEL, await cancelArgs(AP, e2))).after;
  const landedCancel = await cancelArgs(AP, e2);
  await negative('recovery', 'cancel replay: the landed cancel replayed (entry consumed, nonce advanced, nothing pending)', AC, CANCEL, landedCancel, UNKNOWN, [UNKNOWN, INVALID, NOPENDING]);

  // finalised (AF): resubmit, wait out the window (0 s + the 2 s bound), finalise
  const AP2 = (await execute(Original.Contract, AC, 'recover_submit', submitArgs(AC, 0x5e55n, Q, recoveryKey(QR).pk, now() + 2n))).after;
  await new Promise((r) => setTimeout(r, 3500));
  const AF0 = (await execute(Original.Contract, AP2, 'recover_finalise', [])).after;
  const lf = ledgerOf(AF0);
  const finalised: Result = { section: 'recovery', circuit: 'recover_finalise', case: 'finalised (simulator): the set holds only the successor; the plant is the planted device\'s entry at the new epoch and is gone', kind: 'positive' };
  const fOk = lf.devices.size() === 1n && lf.device_epoch === 1n && !lf.devices.member(plant) && Buffer.from(plant).equals(Buffer.from(W.entryAt(AF0.addressBytes, lf.device_epoch, 0n)));
  finalised.positive = { name: finalised.case, verdict: fOk ? 'PASS' : 'FAIL', reason: fOk ? 'state checked' : 'unexpected post-finalise state', proofServer: [], startedAt: new Date().toISOString(), ms: 0 };
  tally(finalised.positive); results.push(finalised); line(finalised);
  // the successor enrols a fresh evm device F and opens a new recovery, so
  // that a cancel has something pending; F's own session is the positive
  const F = await EvmEip712Device.enrol(new SoftwareEvmWallet(0xf0f0n), 'undeployed', 0);
  const fEntry = F.entryAt(AF0.addressBytes, lf.device_epoch, 0n);
  const AF = (await execute(Original.Contract, AF0, 'add_device_with_jubjub', [fEntry, ...authArgs(Q.sign(jubjubChallenges.addDevice({ contractAddress: AF0.addressBytes, authNonce: lf.auth_nonce }, Q.pk, fEntry), 0n))])).after;
  const S3 = sessionOf(0x5e57n);
  await positive('recovery', 'after the recovery: a fresh evm device enrolled by the successor publishes a session (patched path)', posPath, AF, PUBLISH, await pubArgs(AF, S3, F));
  const AFP = (await execute(Original.Contract, AF, 'recover_submit', submitArgs(AF, QR, JubjubDevice.generate(), recoveryKey(0x9e12n).pk, now() + 600n))).after;
  await positive('recovery', 'after the recovery: the fresh evm device cancels a new pending recovery (patched path)', posPath, AFP, CANCEL, await cancelArgs(AFP, F));
  // every old evm_eip712 device, the plant included, refused by membership
  for (const [name, d, ctr] of [['the planted entry\'s device W (counter 0 at the new epoch)', W, 0n], ['the original device', device, 3n], ['the second evm device', e2, 1n]] as const) {
    await negative('recovery', `after the recovery: ${name} publishes`, AF, PUBLISH, await pubArgs(AF, S3, d, undefined, ctr), UNKNOWN, [UNKNOWN]);
    await negative('recovery', `after the recovery: ${name} cancels a pending recovery`, AFP, CANCEL, await cancelArgs(AFP, d, undefined, ctr), UNKNOWN, [UNKNOWN]);
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
