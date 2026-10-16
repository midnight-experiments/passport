// Constraint-level negatives of the `sol_ed25519` arm (spec FR-019), on local
// account states (no deploy, no node, no wallet), proved at the proof server.
//
// For every case:
//   positive   an honest call is proved by the proof server; through a
//              patched module copy, the honest call proved through that copy
//              (its positive control) precedes the copy's first negative of
//              each circuit, so a refusal is the tampering's;
//   simulator  the bad call, executed with the ORIGINAL module, is refused by
//              the generated JavaScript (or the runtime's own type checks)
//              with the expected message;
//   prover     the bad call, executed with the named asserts bypassed (and,
//              where a value the runtime refuses must reach the transcript,
//              named runtime functions overridden), is refused by the proof
//              server, the refusing request being the circuit under test.
//
// Sections (all by default; or name them on the command line):
//   activation   (S2S) the identity key; a wrong blind, salt or key against
//                the boot commitment; small- and mixed-order keys (the
//                runtime's type check, then the proof server's decoding);
//   seam         (S5S) rotate_enc_key_with_sol_ed25519: the binding of every
//                signed member (consistent display inputs), the replays, the
//                frame nibbles (G1E-1), R = O with the verification equation
//                holding, a flipped S bit, inconsistent display inputs; small-
//                and mixed-order R, S + L and QA-1 (a non-canonical limb
//                encoding of the signer's y) at the proof server's decoding;
//   replay       (G1S-3) what another arm's device signs for the same call,
//                the arm's own blind request and another operation's
//                approval, each signed raw by the Solana key;
//   frame        (S6S) the seam owns the frame on the custody exports: the
//                wallet signed a message showing a foreign account;
//   custody      (S6S) append_inbox and withdraw_unshielded: positives,
//                binding, inconsistent display inputs, operation separation,
//                the mirror's over-withdrawal (runtime only, reason recorded);
//   witness      (S6S) withdraw_shielded and withdraw_shielded_to_contract on
//                a local Zswap tree: partial and full spends, then a valid
//                signature over one coin with held_coin answering another
//                (colour, value, nonce, Merkle index);
//   devices      (S7S) add_device for all five target schemes (each entry the
//                target scheme's own derivation), removal by descriptor and by
//                the literal form (Q20), a plant at device_epoch + 1 evicted by
//                descriptor; the binding of each shown descriptor field, the
//                removal's counter, epoch, literal entry and form; the guards
//                under a valid signature (an unregistered tag, unshown fields
//                non-zero, the forms' unshown halves, S13, the last device,
//                Q37's point checks, the seam's A != O);
//   grants       (S8S) issue_grant to sol_ed25519, k256 and passkey grantees,
//                revoke_grant, revoke_all_grants, the grantee twins; binding,
//                the arm's issue rules, Q37, the grant seam's replay, roles
//                (G1S-3) and frame;
//   grantee-scope (G2(S) G2S-1) the three grantee twins at the constraint
//                level, each a VALID grantee approval over an inadmissible
//                call: every scope check on its own (operation not in scope,
//                the object commitment's colour, the caller pin with no
//                contract caller and with another contract — the caller
//                injected into the local call context —, the per-call cap,
//                the spent opening, the cumulative cap, the max coin value,
//                the recipient pin), the record's liveness (revoked, expired,
//                a stale device epoch after a local recover_finalise, a stale
//                generation — unreachable today, built by copying a ledger
//                cell —, an unknown grant id and the record absent after
//                revoke_all_grants, both with the record read answered by a
//                runtime override), the grant seam's R = O, and for the
//                shielded twins the colour assert and the scope's object
//                check each on its own, the four signed substitutions (coin
//                nonce, Merkle index, change entry, encryption key), the coin
//                value, the amount and a stale encryption key;
//   frame-lifecycle (G2(S) G2S-4) the foreign-account frame on add_device,
//                remove_device (both forms), issue_grant, revoke_grant,
//                revoke_all_grants and the two shielded grantee twins (with
//                `frame`, `seam`, `grants` and `recovery`: every gated export);
//   recovery     (S9S) publish_recovery_session_with_sol_ed25519 and
//                recover_cancel_with_sol_ed25519: positives, the binding of
//                every shown operand, operation, nonce and frame, inconsistent
//                display inputs, every assert of the shared chips reached
//                through the arm under a valid signature, the seam, the
//                replays, and after a finalised recovery every old device;
//   qa-s3        (G1S-6) the Field-to-Bytes<32> rendering of the recovery
//                lines is canonical: an approval over the non-canonical
//                rendering (value + r) of each phi and key coordinate;
//   readability  (Q43 words; Q44 = A″, every number in full digits) the
//                message text of the circuits with amounts, caps, an expiry or
//                an RP hash, the honest calls proved, a forged amount, cap or
//                word signed by the wallet, forged digits;
//   rules        (Q46 = A, Q47 = A) a passkey's own RP hash is never zero
//                (add_device, remove_device by descriptor, issue_grant to a
//                passkey grantee) and an any-recipient grant carries no
//                recipient, each refused at the constraint level under a
//                valid signature over the contract's own bytes.
//
// Every prover-level negative records the refusing request's circuit (it must
// be the circuit under test) and the refusal's kind: `constraint` (the
// circuit's relation fails) or `decoding` (the honest proof server could not
// decode an input, which a malicious prover never runs; audit G1E-4). A
// constraint refusal is labelled by how the refused predicate is enforced
// against a malicious prover (audit G2E-4): `constraint` (a relation over the
// call's own inputs) or `constraint on a declared read (+ node transcript
// replay)` (the predicate tests a value the circuit reads from the ledger or
// the call context; the read is a declared public transcript value, so it is
// the node's transcript replay against the real state that refuses a false
// declaration, the constraint holding for the declared value).
//
// Needs a proof server at upstream's endpoint (CONFIG.proofServer); a missing
// proof server is an ERROR, never a pass. SOL_ED25519_DRY=1 runs the
// JavaScript layer only (no proof server; never a verdict of record). Writes
// $EVIDENCE_DIR/sol-ed25519-prover[-<sections>].json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { createHash } from 'node:crypto';
import { ed25519 } from '@noble/curves/ed25519.js';
import { sha512 } from '@noble/hashes/sha2.js';
import { CONFIG } from '../node/wallet.js';
import {
  JubjubDevice, K256Device, K256Grantee, authArgs, grantAuthArgs, jubjubChallenges, k256Challenges, p256Challenges, originHash,
  RECIPIENT_USER_ADDRESS, RECIPIENT_ZSWAP_COIN_PUBLIC_KEY, RECIPIENT_CONTRACT_ADDRESS,
} from '../wallet/signer.js';
import { recoveryKey, signRecoverSubmit, recoverSubmitArgs, recoverSubmitChallenge, JUBJUB_IDENTITY, JUBJUB_ORDER_TWO } from '../wallet/recovery-gate.js';
import { DESCRIPTOR_TAGS, grantOriginHash, padTag } from '../wallet/descriptors.js';
import * as sol from '../wallet/signer-sol-ed25519.js';
import * as msg from '../wallet/sol-ed25519-message.js';
import { softwarePasskey } from './p256-fixtures.js';
import { expectRefusal, expectSuccess, type BypassedContractModule, type NegativeResult, type PositiveResult } from './constraint-negative.js';
import {
  Original, loadPatched, dormant, execute, prove, ledgerOf, proofLog, withLocalCoins, coinStoreAnswering, localCoinPublicKeyBytes,
  transportRetries, overrideState, TYPE_OVERRIDES, QA1_OVERRIDES, SL_OVERRIDES, CALLER_OVERRIDES, callerInjection,
  GRANT_ID_FORGE_OVERRIDES, grantIdForgery, withLedgerCell, type LocalAccount, type LocalCoin,
} from './sol-ed25519-negative.js';

const ALL = ['activation', 'seam', 'replay', 'frame', 'custody', 'witness', 'devices', 'grants', 'grantee-scope', 'frame-lifecycle', 'recovery', 'qa-s3', 'readability', 'rules'];
const SECTIONS = process.argv.slice(2).length ? process.argv.slice(2) : ALL;
for (const s of SECTIONS) if (!ALL.includes(s)) throw new Error(`sol-ed25519-prover: unknown section ${s} (${ALL.join(', ')})`);
const DRY = process.env.SOL_ED25519_DRY === '1';

/** Deterministic bytes, one stream per section (a subset of sections draws
 *  the same values as the full run). */
const rng = (section: string) => {
  let ctr = 0;
  return (n = 32) => {
    const out = new Uint8Array(n);
    const tag = String(ctr++);
    for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(`aa00067/s/sol-ed25519-prover/v1/${section}`).update(tag).update(`/${i}`).digest().subarray(0, Math.min(32, n - i)), i);
    return out;
  };
};
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const fill = (n: number, b: number) => new Uint8Array(n).fill(b);
const Z32 = new Uint8Array(32);
const J = (v: any) => JSON.parse(JSON.stringify(v, (_k, x) => (typeof x === 'bigint' ? x.toString() : x instanceof Uint8Array ? hex(x) : x)));

// circuits
const ACTIVATE = 'activate_initial_device_with_sol_ed25519';
const ROTATE = 'rotate_enc_key_with_sol_ed25519';
const APPEND = 'append_inbox_with_sol_ed25519';
const WU = 'withdraw_unshielded_with_sol_ed25519';
const WS = 'withdraw_shielded_with_sol_ed25519';
const WSC = 'withdraw_shielded_to_contract_with_sol_ed25519';
const ADD = 'add_device_with_sol_ed25519';
const REMOVE = 'remove_device_with_sol_ed25519';
const ISSUE = 'issue_grant_with_sol_ed25519';
const REVOKE = 'revoke_grant_with_sol_ed25519';
const REVOKE_ALL = 'revoke_all_grants_with_sol_ed25519';
const PUBLISH = 'publish_recovery_session_with_sol_ed25519';
const CANCEL = 'recover_cancel_with_sol_ed25519';
const GWU = 'withdraw_unshielded_with_grant_sol_ed25519';
const GWS = 'withdraw_shielded_with_grant_sol_ed25519';
const GWSC = 'withdraw_shielded_to_contract_with_grant_sol_ed25519';
// assert messages
const INVALID = 'invalid signature';
const GINVALID = 'invalid grant signature';
const UNKNOWN = 'unknown device entry';
const BOOT = 'boot commitment mismatch';
const RID = 'R is the identity';
const HEXD = 'display: hex digits do not match the value';
const DIGITS = 'display: digits do not match the value';
const LEADING = 'display: leading zero';
const ALIGN = 'display: not a left-aligned decimal';
const COLOUR = 'held coin colour does not match the withdrawn colour';
const ABOVE = "amount above the spent coin's value";
const INSUFFICIENT = 'insufficient balance';
const NOTREG = 'descriptor: not a registered device tag';
const W117 = 'descriptor: not a 117-byte device tag';
const AUTHORISING = 'cannot remove the authorising device';
const LAST = 'cannot remove last device';
const IDENTITY_KEY = 'Curve25519Point identity is not a permitted ed25519Verify verification key';
const KEY_IS_IDENTITY = 'descriptor: the Ed25519 key is the identity';
const NOT_POINT = "descriptor: the Solana key is not the point's encoding";
const NOT_IN_SCOPE = 'operation not in scope';
const OBJECT = 'scope object mismatch';
const PER_CALL = 'amount above per-call cap';
const SPENT = 'spent opening mismatch';
const CUMULATIVE = 'cumulative cap exceeded';
const PIN = 'recipient not admitted by pin';
const NO_CALLER = 'grant requires a contract caller';
const CALLER_MISMATCH = 'grant caller mismatch';
const MAX_COIN = 'coin above max_coin_value';
const STALE_ENC = 'stale encryption key';
const REVOKED = 'grant revoked';
const EXPIRED = 'grant expired';
const EPOCH = 'grant epoch stale';
const GEN = 'grant generation stale';
const UNKNOWN_GRANT = 'unknown grant';
const PENDING = 'recovery pending; cancel first';
const EMPTY = 'phi must not be empty', RANGE = 'phi length out of range';
const SLOT2 = 'unused phi slot 2 not zero', SLOT3 = 'unused phi slot 3 not zero', SLOT4 = 'unused phi slot 4 not zero';
const SIDZERO = 'session nonce is zero', SIDREUSE = 'session nonce reused', PKREUSE = 'recovery commitment reused';
const IDENT = 'recovery key is the identity', SMALL = 'recovery key has small order';
const NOPENDING = 'no recovery pending';
const FQ = 52435875175126190479447740508185965837690552500527637822603658699938581184513n; // r, the BLS12-381 scalar field
const MAX128 = (1n << 128n) - 1n;
// the order-8 point (RFC 8032 torsion) used for small- and mixed-order values
const T8 = ed25519.Point.fromBytes(Buffer.from('c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a', 'hex'), false);
const aff = (p: any) => { const q = p.toAffine(); return { x: q.x as bigint, y: q.y as bigint }; };

// ═════════════════════════════════════════════════════════════════════════════
// The harness
// ═════════════════════════════════════════════════════════════════════════════

type Expect = string | RegExp;
type RefusalKind = 'constraint' | 'decoding';
type Enforcement = 'constraint' | 'constraint on a declared read (+ node transcript replay)';
interface Result {
  section: string; circuit: string; case: string; kind: 'positive' | 'negative' | 'not applicable' | 'text' | 'state';
  expect?: string; bypassed?: string[]; overrides?: string; mutant?: string;
  positive?: PositiveResult | { verdict: string; reason: string; detail?: string; proofServer?: unknown[] };
  check?: { verdict: string; reason: string };
  simulator?: NegativeResult; prover?: NegativeResult;
  refusal?: { keyLocation?: string; kind: RefusalKind | 'none'; rule?: string; expectedKind: RefusalKind };
  enforcement?: Enforcement; proverLevel?: string; notApplicable?: string;
}
// (G2E-4) asserts whose predicate tests a ledger or call-context read
const READ_ASSERTS = new Set([UNKNOWN, UNKNOWN_GRANT, REVOKED, EPOCH, GEN, EXPIRED, STALE_ENC, PER_CALL, CUMULATIVE, PIN, MAX_COIN, NO_CALLER, CALLER_MISMATCH,
  OBJECT, SPENT, NOT_IN_SCOPE, INSUFFICIENT, 'already activated', BOOT, LAST, PENDING, NOPENDING, SIDREUSE, PKREUSE]);
const enforcementOf = (expect: Expect, name: string): Enforcement =>
  (typeof expect === 'string' && READ_ASSERTS.has(expect))
  || (typeof expect === 'string' && (expect === INVALID || expect === GINVALID) && /replay|nonce advanced|record nonce|stale|landed/i.test(name))
    ? 'constraint on a declared read (+ node transcript replay)' : 'constraint';
const matches = (detail: unknown, e: Expect) => (typeof e === 'string' ? String(detail ?? '').includes(e) : e.test(String(detail ?? '')));

const results: Result[] = [];
let failures = 0, errors = 0;
const tally = (...r: ({ verdict: string } | undefined)[]) => {
  for (const x of r) { if (!x) continue; if (x.verdict === 'FAIL') failures++; if (x.verdict === 'ERROR') errors++; }
};
const strip = <T>(x: T): T => (x ? { ...(x as any), result: undefined } : x);
const line = (r: Result) => {
  const parts = [r.positive && `positive ${r.positive.verdict}`, r.check && `check ${r.check.verdict}`, r.simulator && `simulator ${r.simulator.verdict}`,
    r.prover && `prover ${r.prover.verdict} (${r.prover.layer}${r.refusal ? `, ${r.refusal.kind}${r.refusal.rule ? ` ${r.refusal.rule}` : ''}` : ''})`,
    r.proverLevel && 'runtime only', r.notApplicable && 'not applicable'].filter(Boolean);
  const dry = (r as any).dryCopy as { verdict: string } | undefined;
  if (dry) parts.push(`copy ${dry.verdict} (DRY)`);
  const okAll = [r.positive, r.check, r.simulator, r.prover, dry].every((x) => !x || x.verdict === 'PASS');
  console.log(`  ${okAll ? '✓' : '✗'} [${r.section}] ${r.case}: ${parts.join(', ')}`);
  for (const [k, x] of [['positive', r.positive], ['check', r.check], ['simulator', r.simulator], ['prover', r.prover]] as const) {
    if (x && x.verdict !== 'PASS') console.log(`      ${k}: ${(x as any).reason} ${String((x as any).detail ?? '').slice(0, 500)}`);
  }
};

// One patched copy per (bypass list, overrides), reused across cases; one
// positive control per (copy, circuit).
const copies = new Map<string, BypassedContractModule>();
async function copyFor(bypass: string[], overrides = ''): Promise<BypassedContractModule> {
  const k = JSON.stringify([[...bypass].sort(), overrides]);
  if (!copies.has(k)) copies.set(k, await loadPatched(bypass, overrides));
  return copies.get(k)!;
}
const controlled = new Set<string>();

/** A positive: proved through `mod` (a patched copy, which records it as its
 *  positive control) or the original module; `check` runs on the state
 *  after the call and must return true. Returns that state (or undefined). */
async function positive(section: string, name: string, mod: BypassedContractModule | undefined, a: LocalAccount, circuit: string, args: unknown[],
  check?: (after: LocalAccount) => boolean | Promise<boolean>, hook?: () => void): Promise<LocalAccount | undefined> {
  const r: Result = { section, circuit, case: name, kind: 'positive' };
  let after: LocalAccount | undefined;
  if (DRY) {
    try { hook?.(); after = (await execute((mod ?? Original).Contract, a, circuit, args)).after; r.positive = { verdict: 'PASS', reason: 'DRY: executed (not proved)' }; }
    catch (e: any) { r.positive = { verdict: 'FAIL', reason: 'DRY: execution failed', detail: String(e?.message ?? e) }; }
  } else {
    r.positive = strip(await expectSuccess({ name: `${circuit}: ${name}`, proofLog, through: mod,
      attempt: async () => { hook?.(); const x = await prove((mod ?? Original).Contract, a, circuit, args); after = x.after; return x; } }));
    if (mod && r.positive.verdict === 'PASS') controlled.add(`${mod.file}|${circuit}`);
  }
  if (check && r.positive.verdict === 'PASS') { const okc = await check(after!); r.check = { verdict: okc ? 'PASS' : 'FAIL', reason: okc ? 'state as expected' : 'state check failed' }; }
  tally(r.positive, r.check); results.push(r); line(r);
  return r.positive.verdict === 'PASS' && (!r.check || r.check.verdict === 'PASS') ? after : undefined;
}

interface NegOpts {
  /** the copy the prover level runs (default: copyFor(bypass, overrides)) */
  module?: BypassedContractModule;
  /** runtime overrides of the default copy */
  overrides?: string;
  /** what the overrides do (recorded) */
  overridesLabel?: string;
  /** the module the simulator runs (default: the original) */
  simulatorModule?: BypassedContractModule;
  /** what the simulator must be refused by, when it differs from `expect` */
  simulatorExpect?: Expect;
  /** the arguments the simulator runs, when they differ from the attempt's
   *  (e.g. S + L: the runtime refuses the scalar itself, while the attempt
   *  sends the honest scalar with only its encoding changed) */
  simulatorArgs?: unknown[];
  /** no simulator refusal exists (the tamper is an encoding the JavaScript
   *  never sees): the reason, recorded */
  noSimulator?: string;
  mutant?: string;
  kind?: RefusalKind;
  enforcement?: Enforcement;
  /** run before the simulator, the positive control and the attempt */
  hooks?: { simulator?: () => void; control?: () => void; attempt?: () => void };
  /** run after the case (e.g. clearing an override's target) */
  after?: () => void;
  /** a final check of a PASS (e.g. that an override fired): a reason to FAIL */
  check?: () => string | undefined;
}

/** One negative: refused by the simulator with `expect`, and by the proof
 *  server for `circuit` with `bypass` bypassed, of the expected kind. The
 *  copy first proves `control` (the honest call) through itself, once per
 *  (copy, circuit). */
async function negative(section: string, name: string, a: LocalAccount, circuit: string, args: unknown[], expect: Expect, bypass: string[],
  control: { a: LocalAccount; args: unknown[] } | undefined, opts: NegOpts = {}) {
  const kind = opts.kind ?? 'constraint';
  const r: Result = { section, circuit, case: name, kind: 'negative', expect: String(expect), bypassed: bypass,
    overrides: opts.overridesLabel ?? (opts.overrides ? 'runtime functions overridden' : undefined), mutant: opts.mutant };
  if (kind === 'constraint') r.enforcement = opts.enforcement ?? enforcementOf(expect, name);
  if (opts.noSimulator) (r as any).simulatorLevel = `no JavaScript refusal: ${opts.noSimulator}`;
  else {
    r.simulator = await expectRefusal({ name: `${circuit}: ${name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog,
      attempt: () => { opts.hooks?.simulator?.(); return execute((opts.simulatorModule ?? Original).Contract, a, circuit, opts.simulatorArgs ?? args); } });
    if (r.simulator.verdict === 'PASS' && !matches(r.simulator.detail, opts.simulatorExpect ?? expect)) {
      r.simulator.verdict = 'FAIL'; r.simulator.reason = `refused at runtime, but not by ${String(opts.simulatorExpect ?? expect)}`;
    }
  }
  if (!DRY) {
    const patched = opts.module ?? await copyFor(bypass, opts.overrides ?? '');
    const key = `${patched.file}|${circuit}`;
    r.prover = await expectRefusal({ name: `${circuit}: ${name} (${opts.mutant ?? 'JavaScript checks bypassed'})`,
      expectedLayer: kind === 'decoding' ? 'decoding' : 'prover', bypassed: patched, proofLog, requirePositiveControl: true,
      positiveControl: !controlled.has(key) && control ? () => { opts.hooks?.control?.(); return prove(patched.Contract, control.a, circuit, control.args); } : undefined,
      attempt: () => { opts.hooks?.attempt?.(); return prove(patched.Contract, a, circuit, args); } });
    opts.after?.();
    if (r.prover.positiveControl?.verdict === 'PASS') controlled.add(key);
    const rej = r.prover.rejection;
    r.refusal = { keyLocation: rej?.keyLocation, kind: rej ? (rej.kind as RefusalKind) : 'none', rule: rej?.rule, expectedKind: kind };
    if (r.prover.verdict === 'PASS') {
      // key locations read `contract:<address>/<circuit>?vk=<hash>`
      const refusedCircuit = rej?.keyLocation?.match(/\/([A-Za-z0-9_]+)(\?|$)/)?.[1] ?? rej?.keyLocation;
      if (refusedCircuit !== circuit) { r.prover.verdict = 'FAIL'; r.prover.reason = `refused by ${rej?.keyLocation ?? 'no recorded request'}, not by ${circuit}`; }
      else { const bad = opts.check?.(); if (bad) { r.prover.verdict = 'FAIL'; r.prover.reason = bad; } }
    }
    r.prover = strip(r.prover);
    if (r.prover.positiveControl) r.prover.positiveControl = strip(r.prover.positiveControl);
  } else {
    // DRY: the copy's JavaScript layer — the honest control runs through the
    // copy with no bypassed assert firing, and the attempt runs through it
    // with every bypassed assert firing (what the proof server then sees)
    const patched = opts.module ?? await copyFor(bypass, opts.overrides ?? '');
    const dry: { verdict: string; reason: string; detail?: string } = { verdict: 'PASS', reason: 'DRY: the copy executes the attempt with every bypassed assert firing' };
    try {
      if (control) {
        patched.resetFired(); opts.hooks?.control?.();
        await execute(patched.Contract, control.a, circuit, control.args);
        const f = patched.fired();
        if (f.length) Object.assign(dry, { verdict: 'FAIL', reason: `DRY: the control fired ${f.map((x) => x.message).join('; ')}` });
      }
      if (dry.verdict === 'PASS') {
        patched.resetFired(); opts.hooks?.attempt?.();
        await execute(patched.Contract, a, circuit, args);
        const f = patched.fired().map((x) => x.message);
        const missed = bypass.filter((m) => !f.includes(m));
        if (missed.length) Object.assign(dry, { verdict: 'FAIL', reason: `DRY: bypassed but never fired: ${missed.join('; ')}` });
        else { const bad = opts.check?.(); if (bad) Object.assign(dry, { verdict: 'FAIL', reason: `DRY: ${bad}` }); }
      }
    } catch (e: any) {
      const chain: string[] = []; for (let x = e, i = 0; x && i < 6; x = x.cause, i++) chain.push(String(x?.message ?? x));
      Object.assign(dry, { verdict: 'FAIL', reason: 'DRY: the copy refused the call in JavaScript (it would never reach the proof server)', detail: chain.join(' | ').slice(0, 600) });
      if (process.env.SOL_ED25519_DEBUG) console.error(e);
    }
    opts.after?.();
    (r as any).dryCopy = dry;
    tally(dry);
    if (dry.verdict !== 'PASS') console.log(`      dry copy: ${dry.reason} ${dry.detail ?? ''}`);
  }
  tally(r.simulator, r.prover); results.push(r); line(r);
}

/** A negative that only the generated JavaScript can refuse, with the reason
 *  the prover level is unreachable from a JavaScript-built call (recorded,
 *  never counted as a constraint-level refusal). */
async function runtimeOnly(section: string, name: string, a: LocalAccount, circuit: string, args: unknown[], expect: Expect, why: string) {
  const r: Result = { section, circuit, case: name, kind: 'negative', expect: String(expect) };
  r.simulator = await expectRefusal({ name: `${circuit}: ${name} (generated JavaScript)`, expectedLayer: 'runtime', proofLog,
    attempt: () => execute(Original.Contract, a, circuit, args) });
  if (r.simulator.verdict === 'PASS' && !matches(r.simulator.detail, expect)) { r.simulator.verdict = 'FAIL'; r.simulator.reason = `refused at runtime, but not by ${String(expect)}`; }
  r.proverLevel = `not reachable from a JavaScript-built call: ${why}`;
  tally(r.simulator); results.push(r); line(r);
}
function notApplicable(section: string, circuit: string, name: string, why: string) {
  const r: Result = { section, circuit, case: name, kind: 'not applicable', notApplicable: why };
  results.push(r); line(r);
}
function stateOnly(section: string, name: string, okc: boolean) {
  const r: Result = { section, circuit: '(state)', case: name, kind: 'state', positive: { verdict: okc ? 'PASS' : 'FAIL', reason: okc ? 'state checked (simulator; no proof)' : 'unexpected state', proofServer: [] } };
  tally(r.positive); results.push(r); line(r);
}
function textCheck(section: string, name: string, okc: boolean, detail?: string) {
  const r: Result = { section, circuit: '(message text)', case: name, kind: 'text', positive: { verdict: okc ? 'PASS' : 'FAIL', reason: okc ? "the client's and the circuit's message shows it" : 'not shown', detail } };
  tally(r.positive); results.push(r); line(r);
}

// ── Devices, accounts and messages ──────────────────────────────────────────

type Dev = InstanceType<typeof sol.SolEd25519Device>;
async function solDevice(seed: Uint8Array): Promise<{ seed: Uint8Array; d: Dev }> {
  const s = sol.solSoftwareSigner(seed);
  return { seed, d: sol.SolEd25519Device.fromSigner(s, await sol.deriveSolBlind(s, { network: 'undeployed', accountIndex: 0 })) };
}
const ctxOf = (a: LocalAccount) => ({ contractAddress: a.addressBytes, authNonce: ledgerOf(a).auth_nonce as bigint });
const counterIn = (a: LocalAccount, d: Dev) => { const l = ledgerOf(a); for (let k = 0n; k < 64n; k++) if (l.devices.member(d.entryAt(a.addressBytes, l.device_epoch, k))) return k; return 0n; };
const withShow = (x: any, showArgs: unknown[]) => ({ ...x, showArgs });
const leInt = (b: Uint8Array) => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };
/** A signature with R = O for which [s]B == R + [k]A holds: s = k a mod L (a
 *  the key's secret scalar, from its seed), so only the seam's R != O assert
 *  can refuse it. */
const rIdentityFor = (seed: Uint8Array, key: Uint8Array) => (message: Uint8Array) => {
  const h = sha512(seed).slice(0, 32); h[0] &= 248; h[31] &= 127; h[31] |= 64;
  const a = leInt(h) % sol.ED25519_L;
  const encO = new Uint8Array(32); encO[0] = 1;
  const k = leInt(sha512(new Uint8Array([...encO, ...key, ...message]))) % sol.ED25519_L;
  return { r: { x: 0n, y: 1n }, s: (k * a) % sol.ED25519_L };
};
/** A local account activated by `d` (recovery key `recoverySecret`). */
async function activated(d: Dev, salt: Uint8Array, recoverySecret?: bigint, window?: bigint): Promise<LocalAccount> {
  const rpk = recoverySecret === undefined ? JubjubDevice.generate().pk : recoveryKey(recoverySecret).pk;
  return (await execute(Original.Contract, await dormant(d.bootCommitment(salt), rpk, window), ACTIVATE, d.activationArgs(salt))).after;
}
const issueArgsOf = (g: any, sc: any, s: Uint8Array, au: any, pk: unknown = msg.solTargetPointArg(g)) => [msg.solGranteeArg(g), pk, sc.opWithdrawUnshielded, sc.opWithdrawShielded,
  sc.opWithdrawShieldedToContract, sc.read, sc.color, sc.recipientKind, sc.recipient, sc.maxCoinValue, sc.perCallCap, sc.cap, sc.expiresAt, sc.rpIdHash, sc.readPk,
  sc.windowLen, sc.windowCap, { is_some: sc.caller !== null, value: { bytes: sc.caller ?? Z32 } }, s, ...authArgs(au)];
const scopeOf = (o: any = {}) => ({ opWithdrawUnshielded: false, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: false, color: Z32, recipientKind: 0n,
  recipient: Z32, maxCoinValue: 0n, perCallCap: 0n, cap: 0n, expiresAt: 0n, rpIdHash: Z32, readPk: Z32, windowLen: 0n, windowCap: 0n, caller: null, ...o });

/** The frame negative (G1E-1): the wallet signed the message of `o` showing
 *  a FOREIGN account (its frame nibbles with it); only the seam's frame
 *  check (the display check of the account's hex) can refuse it. */
async function foreignFrameDevice(section: string, rnd: (n?: number) => Uint8Array, a: LocalAccount, d: Dev, site: string, circuit: string, o: any,
  argsOf: (au: any) => unknown[], label = circuit.replace('_with_sol_ed25519', '')) {
  const honest = await sol.authoriseSolDevice(d, ctxOf(a), site, o, counterIn(a, d));
  const frame = JSON.stringify(J(msg.solFrameNibbles(a.addressBytes, d.key)));
  const ix = honest.showArgs.findIndex((x) => JSON.stringify(J(x)) === frame);
  if (ix < 0) throw new Error(`foreignFrame: no frame nibbles in the display inputs of ${circuit}`);
  const foreign = rnd();
  const forged = [...honest.showArgs]; forged[ix] = msg.solFrameNibbles(foreign, d.key);
  const bytes = msg.solMessageBytes(msg.solDeviceMessageText({ site, account: foreign, key: d.key, nonce: ledgerOf(a).auth_nonce as bigint }, o));
  const { sig } = await d.signBytes(bytes);
  await negative(section, `${label}: the wallet signed a message showing a foreign account (seam-owned frame)`, a, circuit,
    argsOf({ ...honest, sig, showArgs: forged }), HEXD, [HEXD], { a, args: argsOf(honest) });
}
async function foreignFrameGrantee(section: string, rnd: (n?: number) => Uint8Array, a: LocalAccount, G: any, ctx: any, site: string, circuit: string, o: any,
  argsOf: (au: any) => unknown[], label = circuit.replace('_sol_ed25519', '')) {
  const honest = await sol.authoriseSolGrantee(G.device, ctx, site, o);
  const frame = JSON.stringify(J(msg.solFrameNibbles(a.addressBytes, G.key)));
  const ix = honest.showArgs.findIndex((x) => JSON.stringify(J(x)) === frame);
  if (ix < 0) throw new Error(`foreignFrame: no frame nibbles in the display inputs of ${circuit}`);
  const foreign = rnd();
  const forged = [...honest.showArgs]; forged[ix] = msg.solFrameNibbles(foreign, G.key);
  const bytes = msg.solMessageBytes(msg.solGranteeMessageText({ site, account: foreign, key: G.key, label: ctx.label, slot: ctx.slot, issuedAt: ctx.issuedAt, nonce: ctx.grantNonce }, o));
  const { sig } = await G.device.signBytes(bytes);
  await negative(section, `${label}: the grantee signed a message showing a foreign account (seam-owned frame)`, a, circuit,
    argsOf({ ...honest, sig, showArgs: forged }), HEXD, [HEXD], { a, args: argsOf(honest) });
}

// ═════════════════════════════════════════════════════════════════════════════
// activation (S2S)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionActivation() {
  const rnd = rng('activation');
  const { d } = await solDevice(rnd());
  const salt = rnd();
  const recoveryPk = JubjubDevice.generate().pk;
  const at = await dormant(d.bootCommitment(salt), recoveryPk);
  const control = { a: at, args: d.activationArgs(salt) };
  await positive('activation', 'honest activation (original module)', undefined, at, ACTIVATE, control.args,
    (after) => ledgerOf(after).booted === true && ledgerOf(after).devices.member(d.entryAt(after.addressBytes, ledgerOf(after).device_epoch, 0n)));
  // the identity: a boot commitment for O committed (computed with the
  // descriptor module's A != O bypassed); only A != O refuses it
  const O = { x: 0n, y: 1n };
  const blindO = rnd();
  const idCopy = await copyFor([KEY_IS_IDENTITY]);
  const atO = await dormant(idCopy.pureCircuits.derive_boot_commitment_with_sol_ed25519(salt, O, blindO), recoveryPk);
  idCopy.resetFired();
  await negative('activation', 'the identity as the device key (its boot commitment committed): refused by the descriptor module\'s A != O', atO, ACTIVATE, [O, salt, blindO], KEY_IS_IDENTITY, [KEY_IS_IDENTITY], control);
  for (const [name, args] of [['wrong blind', [d.pk, salt, rnd()]], ['wrong salt', [d.pk, rnd(), d.blind]],
    ['another key (the committed blind)', [sol.solPublicKeyFromSeed(rnd()).pk, salt, d.blind]]] as [string, unknown[]][]) {
    await negative('activation', name, at, ACTIVATE, args, BOOT, [BOOT], control);
  }
  // small- and mixed-order keys: the runtime's point type refuses them; with
  // the validator overridden the proof server's input decoding does
  for (const [name, p] of [['a small-order key (order 8)', aff(T8)], ['a mixed-order key A + T8', aff(ed25519.Point.fromBytes(d.key, false).add(T8))]] as [string, { x: bigint; y: bigint }][]) {
    const blind = rnd();
    const typeCopy = await copyFor([], TYPE_OVERRIDES);
    const atT = await dormant(typeCopy.pureCircuits.derive_boot_commitment_with_sol_ed25519(salt, p, blind), recoveryPk);
    const before = overrideState.typeBypass;
    await negative('activation', `${name} (honest-toolchain decoding refusal; in-circuit: the subgroup assignment)`, atT, ACTIVATE, [p, salt, blind], /Curve25519Point/, [], control,
      { overrides: TYPE_OVERRIDES, overridesLabel: 'Curve25519Point validator overridden (counted)', kind: 'decoding',
        check: () => (overrideState.typeBypass > before ? undefined : 'the type-check override never fired') });
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// seam (S5S): rotate_enc_key_with_sol_ed25519
// ═════════════════════════════════════════════════════════════════════════════
async function sectionSeam() {
  const rnd = rng('seam');
  const SITE = 'Seam prover test';
  const { seed: seedA, d: device } = await solDevice(rnd());
  const salt = rnd();
  const A0 = await activated(device, salt);
  const k1 = rnd();
  const a1 = await sol.authoriseSolDevice(device, ctxOf(A0), SITE, { op: 'rotate_enc_key', newKey: k1 }, 0n);
  const A1 = await positive('seam', 'honest rotation (nonce 0, counter 0)', undefined, A0, ROTATE, [k1, ...authArgs(a1)])
    ?? (await execute(Original.Contract, A0, ROTATE, [k1, ...authArgs(a1)])).after;
  // negatives at nonce 1, counter 1
  const k2 = rnd();
  const a2 = await sol.authoriseSolDevice(device, ctxOf(A1), SITE, { op: 'rotate_enc_key', newKey: k2 }, 1n);
  const honestArgs = [k2, ...authArgs(a2)];
  const control = { a: A1, args: honestArgs };
  const { d: devB } = await solDevice(rnd());
  const bSig = (await sol.authoriseSolDevice(devB, ctxOf(A1), SITE, { op: 'rotate_enc_key', newKey: k2 }, 1n)).sig;
  const appendSig = (await sol.authoriseSolDevice(device, ctxOf(A1), SITE, { op: 'append_inbox', entry: rnd(192) }, 1n)).sig;
  // display inputs consistent with the executed values; the wallet's signature
  const cons = (newKey: Uint8Array, a: any, site = SITE) =>
    [newKey, ...authArgs({ ...a, showArgs: sol.solDeviceMessageCircuit(device.key, ctxOf(A1), site, { op: 'rotate_enc_key', newKey }).showArgs })];
  const rIdentity = rIdentityFor(seedA, device.key);
  const mDigits = await copyFor([DIGITS]);
  const mHex = await copyFor([HEXD]);
  // a signature over the message rendered with nonce digits "2" (the digit
  // check bypassed in the copy's pure circuit)
  const wrongNonceMsg: Uint8Array = mDigits.pureCircuits.sol_message_rotate_enc_key({ bytes: A1.addressBytes }, device.key, ledgerOf(A1).auth_nonce, k2,
    msg.solShow(SITE, 2n), a2.showArgs[1], a2.showArgs[2]);
  const wrongNonceSig = (await device.signBytes(wrongNonceMsg)).sig;
  // G1E-1: foreign frame nibbles (account; signing key), signed by the wallet
  const foreignAccountFrame = msg.nibblesOf(rnd(), device.key);
  const foreignKeyFrame = msg.nibblesOf(A1.addressBytes, sol.solSoftwareSigner(rnd()).publicKey);
  const frameSig = async (frame: bigint[]) => (await device.signBytes(mHex.pureCircuits.sol_message_rotate_enc_key({ bytes: A1.addressBytes }, device.key,
    ledgerOf(A1).auth_nonce, k2, a2.showArgs[0], frame, a2.showArgs[2]))).sig;
  const NEG: [string, unknown[], Expect, string[]][] = [
    ['binding: another new key at execution (consistent display inputs)', cons(rnd(), a2), INVALID, [INVALID]],
    ['binding: another site label at execution (consistent display inputs)', cons(k2, a2, 'Another site'), INVALID, [INVALID]],
    ["binding: device B's signature with A's key", cons(k2, { ...a2, sig: bSig }), INVALID, [INVALID]],
    ['seam: another use counter', cons(k2, { ...a2, use_counter: 2n }), UNKNOWN, [UNKNOWN]],
    ['seam: another blind', cons(k2, { ...a2, blind: rnd() }), UNKNOWN, [UNKNOWN]],
    ['operation: the signature of another operation (append_inbox)', cons(k2, { ...a2, sig: appendSig }), INVALID, [INVALID]],
    ['replay: the landed signature at the current counter', cons(k1, { ...a1, use_counter: 1n }), INVALID, [INVALID]],
    ['replay: the landed authorisation (consumed entry; its old nonce fails the signature too)', cons(k1, a1), UNKNOWN, [UNKNOWN, INVALID]],
    ['seam: R = O with the verification equation holding (s = k a)', cons(k2, { ...a2, sig: rIdentity(a2.message) }), RID, [RID]],
    ['seam: a flipped S bit', cons(k2, { ...a2, sig: { r: a2.sig.r, s: a2.sig.s ^ 1n } }), INVALID, [INVALID]],
    ['display: the wallet shown nonce 2 while the call executes at nonce 1 (signed over the wrong digits)',
      [k2, ...authArgs({ ...a2, sig: wrongNonceSig, showArgs: [msg.solShow(SITE, 2n), a2.showArgs[1], a2.showArgs[2]] })], DIGITS, [DIGITS]],
    ['display: the hex nibbles of the signed key while another key executes', [rnd(), ...authArgs(a2)], HEXD, [HEXD]],
    ['frame (G1E-1): the frame shows a foreign account (signed over it)', [k2, ...authArgs({ ...a2, sig: await frameSig(foreignAccountFrame), showArgs: [a2.showArgs[0], foreignAccountFrame, a2.showArgs[2]] })], HEXD, [HEXD]],
    ['frame (G1E-1): the frame shows a foreign signing key (signed over it)', [k2, ...authArgs({ ...a2, sig: await frameSig(foreignKeyFrame), showArgs: [a2.showArgs[0], foreignKeyFrame, a2.showArgs[2]] })], HEXD, [HEXD]],
  ];
  for (const [name, args, expect, bypass] of NEG) await negative('seam', name, A1, ROTATE, args, expect, bypass, control);
  // type-level degenerate R (the runtime's point type, then decoding)
  for (const [name, sig] of [['R of small order', { r: aff(T8), s: a2.sig.s }], ['R of mixed order', { r: aff(ed25519.Point.fromAffine(a2.sig.r).add(T8)), s: a2.sig.s }]] as [string, any][]) {
    const before = overrideState.typeBypass;
    await negative('seam', `degenerate: ${name} (honest-toolchain decoding refusal)`, A1, ROTATE, cons(k2, { ...a2, sig }), /Curve25519Point/, [INVALID], control,
      { overrides: TYPE_OVERRIDES, overridesLabel: 'Curve25519Point validator overridden (counted)', kind: 'decoding',
        check: () => (overrideState.typeBypass > before ? undefined : 'the type-check override never fired') });
  }
  // S + L: never a Curve25519Scalar in the runtime; at the proof server, the
  // honest signature's s sent as s + L in the scalar limbs
  {
    const nS = overrideState.nonCanonical;
    await negative('seam', 'degenerate: S + L (the runtime refuses s + L as a scalar; at the proof server the honest s sent as s + L in the scalar limbs: decoding refusal)', A1, ROTATE,
      honestArgs, /Curve25519Scalar|scalar|expected/i, [], control,
      { overrides: SL_OVERRIDES, overridesLabel: 'Curve25519Scalar encoder overridden for the target scalar', kind: 'decoding',
        simulatorArgs: cons(k2, { ...a2, sig: { r: a2.sig.r, s: a2.sig.s + sol.ED25519_L } }),
        hooks: { control: () => { overrideState.scalarTarget = undefined; }, attempt: () => { overrideState.scalarTarget = a2.sig.s; } },
        after: () => { overrideState.scalarTarget = undefined; },
        check: () => (overrideState.nonCanonical > nS ? undefined : 'the scalar encoder override never fired') });
  }
  // QA-1: the honest call with only the signer's point's encoding changed
  {
    const nc = overrideState.nonCanonical;
    await negative('seam', "QA-1: the signer's point with a non-canonical y limb encoding (y - 1 + p) (honest-toolchain decoding refusal)", A1, ROTATE,
      honestArgs, 'non-canonical', [], control,
      { overrides: QA1_OVERRIDES, overridesLabel: 'Curve25519Point encoder overridden for the target point (QA-1)', kind: 'decoding',
        noSimulator: "the JavaScript holds the canonical point; only the limb encoding sent to the proof server is non-canonical",
        hooks: { control: () => { overrideState.target = undefined; }, attempt: () => { overrideState.target = { x: device.pk.x, y: device.pk.y }; } },
        after: () => { overrideState.target = undefined; },
        check: () => (overrideState.nonCanonical > nc ? undefined : 'the point encoder override never fired') });
  }
  await positive('seam', 'the honest rotation at nonce 1 after every refusal (original module)', undefined, A1, ROTATE, honestArgs);
}

// ═════════════════════════════════════════════════════════════════════════════
// replay (G1S-3), frame, custody, witness (S6S)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionCustody() {
  const rnd = rng('custody');
  const SITE = 'S6 custody prover';
  const { d: device } = await solDevice(rnd());
  const A0 = await activated(device, rnd());
  const authFor = (a: LocalAccount, o: any) => sol.authoriseSolDevice(device, ctxOf(a), SITE, o, counterIn(a, device));
  const shownFor = (a: LocalAccount, o: any) => sol.solDeviceMessageCircuit(device.key, ctxOf(a), SITE, o).showArgs;
  const COL_U = fill(32, 0xc1), COL_X = fill(32, 0xc2), RECIPIENT_U = fill(32, 0x77);
  let AU = A0;
  for (const c of [COL_U, COL_X]) AU = (await execute(Original.Contract, AU, 'deposit_unshielded', [c, 1000n])).after;
  const amt = (color: Uint8Array, amount: bigint, decimals = 2, symbol = 'tTOK') => ({ color, amount, decimals, symbol });
  const COL_A = fill(32, 0xa1), COL_B = fill(32, 0xb2), NONCE_H = fill(32, 0x11), NONCE_OTHER = fill(32, 0x12), FILLER = (i: number) => fill(32, 0xf0 + i);
  const shieldedAccount = (coins: { nonce: Uint8Array; color: Uint8Array; value: bigint }[], key: Uint8Array, pick: number) => {
    const { account, coins: placed } = withLocalCoins(A0, coins);
    return { a: { ...account, privateState: coinStoreAnswering([{ key, coin: placed[pick] }]) } as LocalAccount, coin: placed[pick] };
  };
  const RECIPIENT_CONTRACT = fill(32, 0x3c);
  const recipientOf = (circuit: string) => (circuit === WS ? localCoinPublicKeyBytes() : RECIPIENT_CONTRACT);
  const sOp = (circuit: string, amount: bigint, coin: LocalCoin, color = COL_A) => ({
    op: circuit === WS ? 'withdraw_shielded' : 'withdraw_shielded_to_contract', amount: amt(color, amount, 0, 'tA'), recipient: recipientOf(circuit),
    coin: { nonce: coin.nonce, color: coin.color, value: coin.value, mt_index: coin.mtIndex } });
  const sArgs = (circuit: string, amount: bigint, au: any, color = COL_A) => [{ bytes: recipientOf(circuit) }, color, amount, ...authArgs(au)];

  if (SECTIONS.includes('replay')) {
    // what another arm's device signs for the same call, or the arm's own
    // blind request, signed raw by this Solana key; display inputs consistent
    const newKey = rnd();
    const aR = await authFor(A0, { op: 'rotate_enc_key', newKey });
    const ctlR = { a: A0, args: [newKey, ...authArgs(aR)] };
    await positive('replay', 'rotate_enc_key: honest (original module)', undefined, A0, ROTATE, ctlR.args);
    const k = K256Device.generate();
    const pass = softwarePasskey();
    const cctx = ctxOf(A0);
    const cases: [string, Uint8Array][] = [
      ["replay/arm: the k256 arm's rotate_enc_key challenge (same account, nonce, key) signed by the Solana key", k256Challenges.rotateEncKey(cctx, k.pk, newKey)],
      ["replay/arm: the p256 arm's rotate_enc_key challenge (same account, nonce, key) signed by the Solana key", p256Challenges.rotateEncKey(cctx, pass.pk, newKey)],
      ['replay/purpose: the blind request (non-authorising) signed by the same key', sol.solBlindMessage(device.key, { network: 'undeployed', accountIndex: 0 }).bytes],
      ['replay/operation: an append_inbox approval (same frame) signed by the same key', (await authFor(A0, { op: 'append_inbox', entry: rnd(192) })).message],
    ];
    for (const [name, bytes] of cases) {
      const { sig } = await device.signBytes(bytes);
      await negative('replay', name, A0, ROTATE, [newKey, ...authArgs({ ...aR, sig })], INVALID, [INVALID], ctlR);
    }
  }

  if (SECTIONS.includes('frame')) {
    const e = rnd(192);
    await foreignFrameDevice('frame', rnd, A0, device, SITE, APPEND, { op: 'append_inbox', entry: e }, (au) => [e, ...authArgs(au)]);
    await foreignFrameDevice('frame', rnd, AU, device, SITE, WU, { op: 'withdraw_unshielded', amount: amt(COL_U, 10n), recipient: RECIPIENT_U },
      (au) => [COL_U, 10n, { bytes: RECIPIENT_U }, ...authArgs(au)]);
    for (const circuit of [WS, WSC]) {
      const H = shieldedAccount([{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }], COL_A, 1);
      await foreignFrameDevice('frame', rnd, H.a, device, SITE, circuit, sOp(circuit, 300n, H.coin), (au) => sArgs(circuit, 300n, au));
    }
  }

  if (SECTIONS.includes('custody')) {
    const pass = await copyFor([]);
    const E1 = rnd(192), E2 = rnd(192);
    const aE = await authFor(A0, { op: 'append_inbox', entry: E1 });
    const ctlE = { a: A0, args: [E1, ...authArgs(aE)] };
    await positive('custody', 'append_inbox: honest (original module)', undefined, A0, APPEND, ctlE.args,
      (after) => ledgerOf(after).inbox_count === ledgerOf(A0).inbox_count + 1n);
    await negative('custody', 'append_inbox binding: signed E1, executed E2 (consistent display inputs)', A0, APPEND,
      [E2, ...authArgs(withShow(aE, shownFor(A0, { op: 'append_inbox', entry: E2 })))], INVALID, [INVALID], ctlE);
    const E1b = new Uint8Array(E1); E1b[191] ^= 1;
    await negative('custody', 'append_inbox binding: the last ciphertext byte flipped (consistent display inputs)', A0, APPEND,
      [E1b, ...authArgs(withShow(aE, shownFor(A0, { op: 'append_inbox', entry: E1b })))], INVALID, [INVALID], ctlE);
    await negative('custody', "append_inbox display: E2 executed with the signed entry's nibbles", A0, APPEND, [E2, ...authArgs(aE)], HEXD, [HEXD], ctlE);
    const aRot = await authFor(A0, { op: 'rotate_enc_key', newKey: E1.subarray(0, 32) });
    await negative('custody', 'append_inbox operation: a rotate_enc_key signature over the same nonce', A0, APPEND, [E1, ...authArgs({ ...aE, sig: aRot.sig })], INVALID, [INVALID], ctlE);
    const oU = { op: 'withdraw_unshielded', amount: amt(COL_U, 400n), recipient: RECIPIENT_U };
    const aU = await authFor(AU, oU);
    const ctlU = { a: AU, args: [COL_U, 400n, { bytes: RECIPIENT_U }, ...authArgs(aU)] };
    await positive('custody', 'withdraw_unshielded: honest 400 of 1000 (original module)', undefined, AU, WU, ctlU.args,
      (after) => ledgerOf(after).unshielded_balances.lookup(COL_U) === 600n);
    const aU1000 = await authFor(AU, { op: 'withdraw_unshielded', amount: amt(COL_U, 1000n), recipient: RECIPIENT_U });
    await positive('custody', 'withdraw_unshielded: the whole mirror, 1000 (patched path, no bypass)', pass, AU, WU, [COL_U, 1000n, { bytes: RECIPIENT_U }, ...authArgs(aU1000)]);
    const cons = (o: any) => [o.amount.color, o.amount.amount, { bytes: o.recipient }, ...authArgs(withShow(aU, shownFor(AU, o)))];
    await negative('custody', 'withdraw_unshielded binding: amount signed 400, executed 401', AU, WU, cons({ ...oU, amount: amt(COL_U, 401n) }), INVALID, [INVALID], ctlU);
    await negative('custody', 'withdraw_unshielded binding: colour signed U, executed X', AU, WU, cons({ ...oU, amount: amt(COL_X, 400n) }), INVALID, [INVALID], ctlU);
    await negative('custody', 'withdraw_unshielded binding: another recipient', AU, WU, cons({ ...oU, recipient: fill(32, 0x78) }), INVALID, [INVALID], ctlU);
    await negative('custody', "withdraw_unshielded binding: the site's decimal point moved (4.00 shown as 0.400)", AU, WU, cons({ ...oU, amount: amt(COL_U, 400n, 3) }), INVALID, [INVALID], ctlU);
    await negative('custody', "withdraw_unshielded display: 401 executed with the signed amount's digits", AU, WU,
      [COL_U, 401n, { bytes: RECIPIENT_U }, ...authArgs(aU)], DIGITS, [DIGITS], ctlU);
    const aOver = await authFor(AU, { op: 'withdraw_unshielded', amount: amt(COL_U, 1001n), recipient: RECIPIENT_U });
    await runtimeOnly('custody', 'withdraw_unshielded: over-withdrawal (1001 of a 1000 mirror), honestly signed', AU, WU,
      [COL_U, 1001n, { bytes: RECIPIENT_U }, ...authArgs(aOver)], INSUFFICIENT,
      "upstream's shared chip (debit_unshielded); with its assert bypassed, the generated JavaScript's type encoder refuses the negative balance, which is not an assert; in-circuit, the assert and the subtraction's range check refuse it");
    await negative('custody', 'withdraw_unshielded operation: an append_inbox signature over the same nonce', AU, WU,
      [COL_U, 400n, { bytes: RECIPIENT_U }, ...authArgs({ ...aU, sig: (await authFor(AU, { op: 'append_inbox', entry: E1 })).sig })], INVALID, [INVALID], ctlU);
  }

  if (SECTIONS.includes('witness')) {
    for (const circuit of [WS, WSC]) {
      const tag = circuit === WS ? 'withdraw_shielded' : 'withdraw_shielded_to_contract';
      const honestTree = [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }];
      const H = shieldedAccount(honestTree, COL_A, 1);
      const oH = sOp(circuit, 300n, H.coin);
      const aH = await authFor(H.a, oH);
      const ctl = { a: H.a, args: sArgs(circuit, 300n, aH) };
      await positive('witness', `${tag}: honest partial spend 300 of 1000 at index 1 (change 700)`, undefined, H.a, circuit, ctl.args);
      await positive('witness', `${tag}: honest full spend 1000 (change 0)`, undefined, H.a, circuit, sArgs(circuit, 1000n, await authFor(H.a, sOp(circuit, 1000n, H.coin))));
      // colour: the message shows colour A as the Token line, so the
      // signature still verifies: only FR-010's colour assert refuses
      const colour = shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_B, value: 1000n }], COL_A, 1);
      await negative('witness', `${tag}: valid signature for colour A, witness coin of colour B (same nonce, value, index)`, colour.a, circuit, sArgs(circuit, 300n, aH), COLOUR, [COLOUR], ctl);
      const sub = async (label: string, acc: { a: LocalAccount; coin: LocalCoin }) => {
        await negative('witness', `${tag}: ${label} (display inputs consistent with the substitute)`, acc.a, circuit,
          sArgs(circuit, 300n, withShow(aH, shownFor(acc.a, sOp(circuit, 300n, acc.coin)))), INVALID, [INVALID], ctl);
        return acc;
      };
      const value = await sub('valid signature for coin value 1000, witness coin of value 999', shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_A, value: 999n }], COL_A, 1));
      await negative('witness', `${tag}: witness coin of value 999 with the signed coin's digits (display check)`, value.a, circuit, sArgs(circuit, 300n, aH), DIGITS, [DIGITS], ctl);
      const nonce = await sub("valid signature for coin nonce N, witness coin of nonce N'", shieldedAccount([honestTree[0], { nonce: NONCE_OTHER, color: COL_A, value: 1000n }], COL_A, 1));
      await negative('witness', `${tag}: witness coin of nonce N' with the signed nonce's nibbles (display check)`, nonce.a, circuit, sArgs(circuit, 300n, aH), HEXD, [HEXD], ctl);
      const index = await sub('valid signature for Merkle index 1, witness coin H at index 2', shieldedAccount([honestTree[0], { nonce: FILLER(1), color: COL_A, value: 7n }, honestTree[1]], COL_A, 2));
      await negative('witness', `${tag}: witness coin at index 2 with the signed index's digits (display check)`, index.a, circuit, sArgs(circuit, 300n, aH), DIGITS, [DIGITS], ctl);
      const small = shieldedAccount([honestTree[0], { nonce: NONCE_H, color: COL_A, value: 200n }], COL_A, 1);
      await runtimeOnly('witness', `${tag}: witness coin of value 200 below the signed amount 300`, small.a, circuit, sArgs(circuit, 300n, aH), ABOVE,
        "the client renderer refuses to build such a message (no change digits exist); with the arm's assert bypassed, the change (value - amount) is negative and the generated JavaScript's type encoder refuses it, which is not an assert; in-circuit, the assert, the subtraction's range check and the signature over the shown value refuse it");
    }
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// devices (S7S)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionDevices() {
  const rnd = rng('devices');
  const SITE = 'S7 devices prover';
  const { d: S } = await solDevice(rnd());
  const A0 = await activated(S, rnd());
  const authFor = (a: LocalAccount, o: any, d = S) => sol.authoriseSolDevice(d, ctxOf(a), SITE, o, counterIn(a, d));
  const shownFor = (a: LocalAccount, o: any) => sol.solDeviceMessageCircuit(S.key, ctxOf(a), SITE, o).showArgs;
  const live = (a: LocalAccount, e: Uint8Array) => ledgerOf(a).devices.member(e);
  const epochOf = (a: LocalAccount) => ledgerOf(a).device_epoch as bigint;
  const leN = (v: bigint, n: number) => { const o = new Uint8Array(n); let x = v; for (let i = 0; i < n; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
  // the evm_eip712 entry by the spec preimage pad32(tag) || account || address(20) || blind(32) || le4(epoch) || le8(counter)
  const evmEntry = (account: Uint8Array, address: Uint8Array, blind: Uint8Array, e: bigint, c: bigint): Uint8Array =>
    new Uint8Array(createHash('sha256').update(padTag(DESCRIPTOR_TAGS.device.evm_eip712)).update(account).update(address).update(blind).update(leN(e, 4)).update(leN(c, 8)).digest());
  const jub = JubjubDevice.generate();
  const k1 = K256Device.generate();
  const pass = softwarePasskey();
  const evmAddr = rnd(20), evmBlind = rnd();
  const { d: S2 } = await solDevice(rnd());
  const targets: [string, any, (addr: Uint8Array, epoch: bigint, counter: bigint) => Uint8Array][] = [
    ['jubjub', { scheme: 'jubjub', x: jub.pk.x, y: jub.pk.y }, (a, e, c) => jub.entryAt(a, e, c)],
    ['k256', { scheme: 'k256', x: k1.pk.x, y: k1.pk.y, envelope: Number(k1.envelope) }, (a, e, c) => k1.entryAt(a, e, c)],
    ['p256', { scheme: 'p256', x: pass.pk.x, y: pass.pk.y, policy: { rpIdHash: pass.policy.rp_id_hash, origin: pass.policy.origin } }, (a, e, c) => pass.device.entryAt(a, e, c)],
    ['evm_eip712', { scheme: 'evm_eip712', address: evmAddr, blind: evmBlind }, (a, e, c) => evmEntry(a, evmAddr, evmBlind, e, c)],
    ['sol_ed25519', S2.descriptor(), (a, e, c) => S2.entryAt(a, e, c)],
  ];
  const addArgs = (t: any, au: any) => [msg.solTargetArg(t), msg.solTargetPointArg(t), ...authArgs(au)];
  const pass0 = await copyFor([]);
  for (const [scheme, d, entryOf] of targets) {
    const t = sol.solTargetOf(d);
    const au = await authFor(A0, { op: 'add_device', target: t });
    const ep = epochOf(A0);
    await positive('devices', `add_device: a ${scheme} target by descriptor; the entry equals ${scheme === 'evm_eip712' ? 'the spec recipe (SHA-256, recomputed)' : `the ${scheme} arm's own derivation`} at (epoch, 0); nothing at epoch + 1`,
      scheme === 'jubjub' ? pass0 : undefined, A0, ADD, addArgs(t, au),
      (after) => live(after, entryOf(after.addressBytes, ep, 0n)) && !live(after, entryOf(after.addressBytes, ep + 1n, 0n)) && ledgerOf(after).device_count === 2n);
  }
  // A1: S plus J, K and the passkey P
  let A1 = A0;
  for (const [, d] of targets.slice(0, 3)) {
    const t = sol.solTargetOf(d);
    A1 = (await execute(Original.Contract, A1, ADD, addArgs(t, await authFor(A1, { op: 'add_device', target: t })))).after;
  }
  const tJ = sol.solTargetOf(targets[0][1]), tK = sol.solTargetOf(targets[1][1]), tP = sol.solTargetOf(targets[2][1]);
  const ep1 = epochOf(A1);
  const IDP = { x: 0n, y: 1n };
  const remArgs = (literal: boolean, t: any, counter: bigint, epoch: bigint, entry: Uint8Array, au: any) => [literal, msg.solTargetArg(t), literal ? IDP : msg.solTargetPointArg(t), counter, epoch, entry, ...authArgs(au)];
  const oRemJ = { op: 'remove_device', literal: false, target: tJ, counter: 0n, epoch: ep1 };
  const ctlRem = { a: A1, args: remArgs(false, tJ, 0n, ep1, new Uint8Array(32), await authFor(A1, oRemJ)) };
  await positive('devices', 'remove_device by descriptor: the jubjub device J at (epoch, 0)', undefined, A1, REMOVE, ctlRem.args,
    (after) => !live(after, jub.entryAt(after.addressBytes, ep1, 0n)) && ledgerOf(after).device_count === 3n);
  const eK = k1.entryAt(A1.addressBytes, ep1, 0n);
  const ctlLit = { a: A1, args: remArgs(true, { tag: '' }, 0n, 0n, eK, await authFor(A1, { op: 'remove_device', literal: true, entry: eK })) };
  await positive('devices', 'remove_device by the literal form ("Removes a device this wallet cannot identify"): K\'s entry', undefined, A1, REMOVE, ctlLit.args,
    (after) => !live(after, eK) && ledgerOf(after).device_count === 3n);
  // the future-epoch plant: K enrols a sol entry at device_epoch + 1 through
  // upstream's raw add_device_with_k256; S evicts it by descriptor at that epoch
  const { d: Wd } = await solDevice(rnd());
  const plant = Wd.entryAt(A1.addressBytes, ep1 + 1n, 0n);
  const kAuth = k1.sign(k256Challenges.addDevice({ contractAddress: A1.addressBytes, authNonce: ledgerOf(A1).auth_nonce }, k1.pk, plant), 0n);
  const A2 = await positive('devices', 'plant: the upstream residual — k256 device K plants a sol_ed25519 entry at device_epoch + 1 (raw add_device_with_k256)', undefined, A1, 'add_device_with_k256', [plant, ...authArgs(kAuth)],
    (after) => live(after, plant));
  if (A2) {
    const tW = sol.solTargetOf(Wd.descriptor());
    const au = await authFor(A2, { op: 'remove_device', literal: false, target: tW, counter: 0n, epoch: ep1 + 1n });
    await positive('devices', 'plant: S evicts the planted entry by descriptor at target epoch device_epoch + 1', undefined, A2, REMOVE, remArgs(false, tW, 0n, ep1 + 1n, new Uint8Array(32), au),
      (after) => !live(after, plant));
  }
  // binding: a shown field changed at execution (consistent display inputs)
  const consAdd = async (a: LocalAccount, signed: any, executed: any) => {
    const au = await authFor(a, { op: 'add_device', target: signed });
    return addArgs(executed, withShow(au, shownFor(a, { op: 'add_device', target: executed })));
  };
  const ctlAdd = { a: A0, args: addArgs(tJ, await authFor(A0, { op: 'add_device', target: tJ })) };
  const flip = (b: Uint8Array) => { const o = new Uint8Array(b); o[0] ^= 1; return o; };
  const tE = sol.solTargetOf(targets[3][1]), tS2 = sol.solTargetOf(targets[4][1]);
  const B: [string, any, any][] = [
    ['the jubjub x coordinate', tJ, { ...tJ, a: flip(tJ.a!) }],
    ['the k256 envelope (0 -> 1)', tK, { ...tK, envelope: 1n }],
    ['the passkey origin', tP, { ...tP, origin: new TextEncoder().encode('https://b.example.com') }],
    ['the passkey RP hash', tP, { ...tP, c: flip((tP as any).c) }],
    ['the evm address', tE, { ...tE, address: flip((tE as any).address) }],
    ['the sol key (another valid key)', tS2, { ...tS2, a: sol.solSoftwareSigner(rnd()).publicKey }],
    ['the device privacy salt (sol)', tS2, { ...tS2, b: flip((tS2 as any).b) }],
    ['the scheme: a jubjub key signed, the same bytes executed as an evm target', tJ, { tag: DESCRIPTOR_TAGS.device.evm_eip712, address: new Uint8Array(20), a: tJ.a }],
  ];
  for (const [name, signed, executed] of B) await negative('devices', `binding: add_device, ${name} changed at execution`, A0, ADD, await consAdd(A0, signed, executed), INVALID, [INVALID], ctlAdd);
  const consRem = async (signed: any, executed: any, a: LocalAccount = A1) => {
    const au = await authFor(a, signed);
    return executed.literal ? remArgs(true, { tag: '' }, 0n, 0n, executed.entry, withShow(au, shownFor(a, executed)))
      : remArgs(false, executed.target, executed.counter, executed.epoch, new Uint8Array(32), withShow(au, shownFor(a, executed)));
  };
  // the executed (epoch, counter) must name a LIVE entry: K plants J's entry there first
  const kPlant = async (a: LocalAccount, entry: Uint8Array) => {
    const l = ledgerOf(a);
    const kc = (() => { for (let c = 0n; c < 64n; c++) if (l.devices.member(k1.entryAt(a.addressBytes, l.device_epoch, c))) return c; throw new Error('K not live'); })();
    const ka = k1.sign(k256Challenges.addDevice({ contractAddress: a.addressBytes, authNonce: l.auth_nonce }, k1.pk, entry), kc);
    return (await execute(Original.Contract, a, 'add_device_with_k256', [entry, ...authArgs(ka)])).after;
  };
  {
    const Ac = await kPlant(A1, jub.entryAt(A1.addressBytes, ep1, 1n));
    const ctlRc = { a: Ac, args: remArgs(false, tJ, 0n, ep1, new Uint8Array(32), await authFor(Ac, oRemJ)) };
    await negative('devices', "binding: remove_device, the counter changed at execution (0 -> 1; J's counter-1 entry live)", Ac, REMOVE, await consRem(oRemJ, { ...oRemJ, counter: 1n }, Ac), INVALID, [INVALID], ctlRc);
    const Ae = await kPlant(A1, jub.entryAt(A1.addressBytes, ep1 + 1n, 0n));
    const ctlRe = { a: Ae, args: remArgs(false, tJ, 0n, ep1, new Uint8Array(32), await authFor(Ae, oRemJ)) };
    await negative('devices', "binding: remove_device, the epoch changed at execution (J's entry at epoch + 1 live)", Ae, REMOVE, await consRem(oRemJ, { ...oRemJ, epoch: ep1 + 1n }, Ae), INVALID, [INVALID], ctlRe);
  }
  await negative('devices', 'binding: remove_device, the literal entry changed at execution', A1, REMOVE,
    await consRem({ op: 'remove_device', literal: true, entry: eK }, { op: 'remove_device', literal: true, entry: jub.entryAt(A1.addressBytes, ep1, 0n) }), INVALID, [INVALID], ctlRem);
  await negative('devices', "binding: remove_device, the form swapped (a literal approval of J's entry executed as J's descriptor)", A1, REMOVE,
    await consRem({ op: 'remove_device', literal: true, entry: jub.entryAt(A1.addressBytes, ep1, 0n) }, oRemJ), INVALID, [INVALID], ctlRem);
  // guards (audit G1(S) F-A8) under a VALID signature
  {
    // an unregistered tag: the message shows the class's tag text (the
    // passkey's), signed only with the tag check bypassed in the copy's pure circuit
    const mTag = await copyFor([NOTREG, W117]);
    const badArg = { ...msg.solTargetArg(tP), tag: padTag('midnight:account:device:zz:v9') };
    const shown = shownFor(A0, { op: 'add_device', target: tP });
    const bytes = mTag.pureCircuits.sol_message_add_device({ bytes: A0.addressBytes }, S.key, ledgerOf(A0).auth_nonce, badArg, ...shown);
    const { sig } = await S.signBytes(bytes);
    const au = { ...(await authFor(A0, { op: 'add_device', target: tP })), sig };
    await negative('devices', 'guards: add_device, an unregistered tag under a valid signature (the message shows the passkey class text)', A0, ADD, [badArg, IDP, ...authArgs(au)], NOTREG, [NOTREG, W117],
      { a: A0, args: addArgs(tP, await authFor(A0, { op: 'add_device', target: tP })) });
  }
  {
    const odd = { ...msg.solTargetArg(tJ), envelope: 1n };
    const au = await authFor(A0, { op: 'add_device', target: tJ });
    const shE = au.showArgs as any[];
    await negative('devices', 'guards: add_device, a jubjub target carrying a non-zero envelope (not shown; refused by the canonical-descriptor check)', A0, ADD,
      [odd, msg.solTargetPointArg(tJ), ...authArgs(withShow(au, [msg.solTargetShow({ ...tJ, envelope: 1n } as any), shE[1], shE[2], shE[3]]))], 'descriptor: unused envelope must be zero', ['descriptor: unused envelope must be zero'], ctlAdd);
    const oddAddr = { ...msg.solTargetArg(tJ), address: rnd(20) };
    await negative('devices', 'guards: add_device, a jubjub target carrying a non-zero address (not shown; refused by the canonical-descriptor check)', A0, ADD,
      [oddAddr, msg.solTargetPointArg(tJ), ...authArgs(withShow(au, shownFor(A0, { op: 'add_device', target: { ...tJ, address: oddAddr.address } })))], 'descriptor: unused address must be zero', ['descriptor: unused address must be zero'], ctlAdd);
  }
  {
    const au = await authFor(A1, oRemJ);
    const hexWith = sol.solDeviceMessageCircuit(S.key, ctxOf(A1), SITE, oRemJ as any).showArgs as any[];
    const nib = msg.nibblesOf(...msg.solDeviceHexValues({ op: 'remove_device', literal: false, target: tJ, counter: 0n, epoch: ep1 } as any).slice(0, 4), eK);
    await negative('devices', 'guards: remove_device descriptor form carrying a non-zero literal entry (not shown; never executed)', A1, REMOVE,
      [false, msg.solTargetArg(tJ), msg.solTargetPointArg(tJ), 0n, ep1, eK, ...authArgs(withShow(au, [hexWith[0], hexWith[1], hexWith[2], nib]))], 'remove_device: a descriptor removal carries no literal entry',
      ['remove_device: a descriptor removal carries no literal entry'], ctlRem);
    const auL = await authFor(A1, { op: 'remove_device', literal: true, entry: eK });
    const lsh = sol.solDeviceMessageCircuit(S.key, ctxOf(A1), SITE, { op: 'remove_device', literal: true, entry: eK } as any).showArgs as any[];
    const nibL = msg.nibblesOf(...msg.solDeviceHexValues({ op: 'remove_device', literal: false, target: tJ, counter: 0n, epoch: 0n } as any).slice(0, 4), eK);
    await negative('devices', 'guards: remove_device literal form carrying a non-zero descriptor (not shown; never executed)', A1, REMOVE,
      [true, msg.solTargetArg(tJ), IDP, 0n, 0n, eK, ...authArgs(withShow(auL, [lsh[0], lsh[1], lsh[2], nibL]))], 'remove_device: a literal removal carries no descriptor',
      ['remove_device: a literal removal carries no descriptor'], ctlLit);
  }
  {
    const c = counterIn(A1, S);
    const tS = sol.solTargetOf(S.descriptor());
    const oS = { op: 'remove_device', literal: false, target: tS, counter: c + 1n, epoch: ep1 };
    await negative('devices', 'guards: S13, S removes its own post-roll entry by descriptor', A1, REMOVE, remArgs(false, tS, c + 1n, ep1, new Uint8Array(32), await authFor(A1, oS)), AUTHORISING, [AUTHORISING], ctlRem);
    const ownNext = S.entryAt(A1.addressBytes, ep1, c + 1n);
    await negative('devices', 'guards: S13, S removes its own post-roll entry by the literal form', A1, REMOVE,
      remArgs(true, { tag: '' }, 0n, 0n, ownNext, await authFor(A1, { op: 'remove_device', literal: true, entry: ownNext })), AUTHORISING, [AUTHORISING], ctlLit);
    const lone = rnd();
    await negative('devices', 'guards: the last device, S alone removes another entry (literal form)', A0, REMOVE,
      remArgs(true, { tag: '' }, 0n, 0n, lone, await authFor(A0, { op: 'remove_device', literal: true, entry: lone })), LAST, [LAST, UNKNOWN], { a: A1, args: ctlLit.args });
  }
  // Q37 = B: a Solana target is a point whose encoding the circuit derives
  {
    const other = sol.solSoftwareSigner(rnd()).publicKey;
    const au = await authFor(A0, { op: 'add_device', target: tS2 });
    await negative('devices', 'guards (Q37): a sol target whose point is another key than the bytes shown (only the in-circuit derivation refuses)', A0, ADD,
      [msg.solTargetArg(tS2), msg.solTargetPoint(other), ...authArgs(au)], NOT_POINT, [NOT_POINT], ctlAdd);
    const auJ = await authFor(A0, { op: 'add_device', target: tJ });
    await negative('devices', 'guards (Q37): a jubjub target carrying a non-identity point (not shown; refused by the canonical-descriptor check)', A0, ADD,
      [msg.solTargetArg(tJ), msg.solTargetPoint(other), ...authArgs(auJ)], 'descriptor: unused point must be the identity', ['descriptor: unused point must be the identity'], ctlAdd);
    // the identity as a sol target: the message renders 0100..00 and the
    // wallet signs it; only the derivation's A != O refuses
    const idKey = new Uint8Array(32); idKey[0] = 1;
    const tId = { tag: DESCRIPTOR_TAGS.device.sol_ed25519, a: idKey, b: rnd() };
    const idArg = { ...msg.solTargetArg({ tag: 'midnight:account:device:v1' } as any), tag: padTag(DESCRIPTOR_TAGS.device.sol_ed25519), a: idKey, b: tId.b };
    const shownId = [msg.solTargetShow(tId as any), msg.solShow(SITE, ledgerOf(A0).auth_nonce), msg.solFrameNibbles(A0.addressBytes, S.key), msg.nibblesOf(...msg.solDeviceHexValues({ op: 'add_device', target: tId } as any))];
    const idBytes = Original.pureCircuits.sol_message_add_device({ bytes: A0.addressBytes }, S.key, ledgerOf(A0).auth_nonce, idArg, ...shownId);
    const auId = { ...au, sig: (await S.signBytes(idBytes)).sig, showArgs: shownId };
    await negative('devices', 'guards (Q37): the identity point as a sol target (its encoding 0100..00 shown and signed): refused by A != O in the derivation', A0, ADD,
      [idArg, { x: 0n, y: 1n }, ...authArgs(auId)], KEY_IS_IDENTITY, [KEY_IS_IDENTITY], ctlAdd);
  }
  // the seam's A != O: an identity sol entry planted through an upstream
  // arm's raw add_device (that pure derivation checks no key), then a call
  // for the identity key
  {
    const idKey = new Uint8Array(32); idKey[0] = 1; // the RFC 8032 encoding of O = (0, 1)
    const idBlind = rnd();
    const kA = ledgerOf(A1);
    const le = (v: bigint, n: number) => { const o = new Uint8Array(n); let x = v; for (let i = 0; i < n; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
    const idEntry = new Uint8Array(createHash('sha256').update(new Uint8Array([...padTag(DESCRIPTOR_TAGS.device.sol_ed25519), ...A1.addressBytes, ...idKey, ...idBlind, ...le(kA.device_epoch, 4), ...le(0n, 8)])).digest());
    const kc = (() => { for (let c = 0n; c < 64n; c++) if (kA.devices.member(k1.entryAt(A1.addressBytes, kA.device_epoch, c))) return c; throw new Error('K not live'); })();
    const kAuth2 = k1.sign(k256Challenges.addDevice({ contractAddress: A1.addressBytes, authNonce: kA.auth_nonce }, k1.pk, idEntry), kc);
    const AO = await positive('devices', "guards (e) setup: k256 device K plants the identity's sol entry (raw add_device_with_k256; the pure derivation checks no key)", undefined, A1, 'add_device_with_k256', [idEntry, ...authArgs(kAuth2)],
      (after) => live(after, idEntry));
    if (AO) {
      // a signature valid for A = O: R = [s]B, so [s]B == R + [k]O holds
      const sc = 12345678901234567890n;
      const R = ed25519.Point.BASE.multiply(sc).toAffine();
      const newKey = rnd();
      const idShow = sol.solDeviceMessageCircuit(idKey, ctxOf(AO), SITE, { op: 'rotate_enc_key', newKey }).showArgs;
      const auth = { pk: { x: 0n, y: 1n }, blind: idBlind, use_counter: 0n, sig: { r: { x: R.x, y: R.y }, s: sc } };
      const honestRot = await authFor(AO, { op: 'rotate_enc_key', newKey });
      await negative('devices', "guards (e): the seam's A != O — a call signed for the identity key (its entry planted, the verification equation holding) is refused only by A != O (the descriptor module's signer derivation and ed25519Verify)", AO, ROTATE,
        [newKey, ...idShow, auth], KEY_IS_IDENTITY, [KEY_IS_IDENTITY, IDENTITY_KEY], { a: AO, args: [newKey, ...authArgs(honestRot)] });
    }
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// grants (S8S)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionGrants() {
  const rnd = rng('grants');
  const SITE = 'S8 grants prover';
  const { d: S } = await solDevice(rnd());
  const A0 = await activated(S, rnd());
  const authFor = (a: LocalAccount, o: any) => sol.authoriseSolDevice(S, ctxOf(a), SITE, o, counterIn(a, S));
  const shownFor = (a: LocalAccount, o: any) => sol.solDeviceMessageCircuit(S.key, ctxOf(a), SITE, o).showArgs;
  const gSigner = sol.solSoftwareSigner(rnd());
  const G = await sol.SolEd25519Grantee.enrol(gSigner, { network: 'undeployed', issuingAccount: A0.addressBytes }, 'Example dApp');
  const K = K256Grantee.generate();
  const ohK = originHash('https://k.example');
  const pass = softwarePasskey();
  const gG = G.grantee(0n);
  const gK = sol.solGranteeOf({ scheme: 'k256', x: K.pk.x, y: K.pk.y, envelope: 0 } as any, { originHash: ohK }, 0n);
  const gP = sol.solGranteeOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y } as any, { origin: pass.policy.origin }, 0n);
  const COL_U = fill(32, 0xc1), PINNED = fill(32, 0x77);
  const scope = (o: any = {}) => scopeOf({ opWithdrawUnshielded: true, color: COL_U, maxCoinValue: 600n, perCallCap: 600n, cap: 1000n, ...o });
  const sU = scope({ recipientKind: RECIPIENT_USER_ADDRESS, recipient: PINNED });
  const saltU = rnd();
  const auG = await authFor(A0, { op: 'issue_grant', grantee: gG, ...sU });
  const ctlIssue = { a: A0, args: issueArgsOf(gG, sU, saltU, auG) };
  const A1 = await positive('grants', 'issue_grant to a sol_ed25519 grantee (unshielded, recipient pinned)', undefined, A0, ISSUE, ctlIssue.args,
    (after) => ledgerOf(after).grants.member(G.grantId(after.addressBytes, 0n)));
  await positive('grants', 'issue_grant to a k256 grantee (the Q17 labelled origin hash)', undefined, A0, ISSUE, issueArgsOf(gK, sU, rnd(), await authFor(A0, { op: 'issue_grant', grantee: gK, ...sU })),
    (after) => ledgerOf(after).grants.member(K.grantId(after.addressBytes, ohK, 0n)));
  const sP = scope({ opWithdrawUnshielded: false, read: true, readPk: rnd(), rpIdHash: pass.policy.rp_id_hash, color: Z32, maxCoinValue: 0n, perCallCap: 0n, cap: 0n });
  await positive('grants', 'issue_grant to a passkey grantee (read-only, its RP hash)', undefined, A0, ISSUE, issueArgsOf(gP, sP, rnd(), await authFor(A0, { op: 'issue_grant', grantee: gP, ...sP })),
    (after) => ledgerOf(after).grants.member(pass.grantee.grantId(after.addressBytes, grantOriginHash(pass.policy.origin), 0n)));
  const cons = (signed: any, eg: any, esc: any) => issueArgsOf(eg, esc, saltU, withShow(signed, shownFor(A0, { op: 'issue_grant', grantee: eg, ...esc })));
  await negative('grants', 'issue binding: the cap changed at execution', A0, ISSUE, cons(auG, gG, { ...sU, cap: 999n }), INVALID, [INVALID], ctlIssue);
  await negative('grants', 'issue binding: a caller pin added at execution', A0, ISSUE, cons(auG, gG, { ...sU, caller: rnd() }), INVALID, [INVALID], ctlIssue);
  await negative('grants', 'issue binding: the grantee label changed', A0, ISSUE, cons(auG, { ...gG, label: 'Other dApp' }, sU), INVALID, [INVALID], ctlIssue);
  await negative('grants', 'issue binding: the grantee slot changed', A0, ISSUE, cons(auG, { ...gG, slot: 1n }, sU), INVALID, [INVALID], ctlIssue);
  const auK = await authFor(A0, { op: 'issue_grant', grantee: gK, ...sU });
  const flip = (b: Uint8Array) => { const o = new Uint8Array(b); o[0] ^= 1; return o; };
  await negative('grants', "issue binding: the k256 grantee's labelled origin hash changed (Q17)", A0, ISSUE, cons(auK, { ...gK, originHash: flip(ohK) }, sU), INVALID, [INVALID], ctlIssue);
  const sRead = scope({ readPk: rnd() });
  await negative('grants', 'issue rule: a read key without read (valid signature)', A0, ISSUE, issueArgsOf(gG, sRead, saltU, await authFor(A0, { op: 'issue_grant', grantee: gG, ...sRead })),
    'sol_ed25519: a read key without read', ['sol_ed25519: a read key without read'], ctlIssue);
  const sRp = scope({ rpIdHash: rnd() });
  await negative('grants', 'issue rule: an RP hash on a non-passkey grantee (valid signature)', A0, ISSUE, issueArgsOf(gG, sRp, saltU, await authFor(A0, { op: 'issue_grant', grantee: gG, ...sRp })),
    'sol_ed25519: an RP hash belongs to a passkey grantee', ['sol_ed25519: an RP hash belongs to a passkey grantee'], ctlIssue);
  await negative('grants', 'issue (Q37): the grantee point is another key than the bytes shown (valid signature)', A0, ISSUE,
    issueArgsOf(gG, sU, saltU, auG, msg.solTargetPoint(sol.solSoftwareSigner(rnd()).publicKey)), NOT_POINT, [NOT_POINT], ctlIssue);
  if (A1) {
    const auR = await authFor(A1, { op: 'revoke_grant', grantee: gG });
    const ctlRev = { a: A1, args: [msg.solGranteeArg(gG), msg.solTargetPointArg(gG), ...authArgs(auR)] };
    await positive('grants', 'revoke_grant by descriptor', undefined, A1, REVOKE, ctlRev.args, (after) => ledgerOf(after).grants.lookup(G.grantId(after.addressBytes, 0n)).active === false);
    // a second live grant to G at slot 1, so the executed slot exists and only the signature refuses
    const A1s = (await execute(Original.Contract, A1, ISSUE, issueArgsOf(G.grantee(1n), sU, rnd(), await authFor(A1, { op: 'issue_grant', grantee: G.grantee(1n), ...sU })))).after;
    const auRs = await authFor(A1s, { op: 'revoke_grant', grantee: gG });
    const ctlRevS = { a: A1s, args: [msg.solGranteeArg(gG), msg.solTargetPointArg(gG), ...authArgs(auRs)] };
    await negative('grants', 'revoke binding: another slot executed (a live grant at slot 1; the approval names slot 0)', A1s, REVOKE,
      [msg.solGranteeArg({ ...gG, slot: 1n }), msg.solTargetPointArg(gG), ...authArgs(withShow(auRs, shownFor(A1s, { op: 'revoke_grant', grantee: { ...gG, slot: 1n } })))], INVALID, [INVALID], ctlRevS);
    const auAll = await authFor(A1, { op: 'revoke_all_grants' });
    const ctlAll = { a: A1, args: authArgs(auAll) };
    await positive('grants', 'revoke_all_grants', undefined, A1, REVOKE_ALL, ctlAll.args, (after) => ledgerOf(after).grant_generation === ledgerOf(A1).grant_generation + 1n);
    const cancelSig = (await authFor(A1, { op: 'recover_cancel' })).sig;
    await negative('grants', 'revoke_all operation: a recover_cancel signature presented as revoke_all_grants', A1, REVOKE_ALL, authArgs({ ...auAll, sig: cancelSig }), INVALID, [INVALID], ctlAll);
  }
  // the grant seam
  if (A1) {
    const AU = (await execute(Original.Contract, A1, 'deposit_unshielded', [COL_U, 1000n])).after;
    const opening = (spent: bigint) => ({ originHash: grantOriginHash(msg.labelBytes(G.label)), slot: 0n, scopeSalt: saltU, recipientKind: RECIPIENT_USER_ADDRESS, pinnedRecipient: PINNED, maxCoinValue: 600n, spentPrev: spent });
    const gctx = (a: LocalAccount, slot = 0n, g: any = G) => { const r = ledgerOf(a).grants.lookup(g.grantId(a.addressBytes, slot)); return { contractAddress: a.addressBytes, label: g.label, slot, issuedAt: r.issued_at, grantNonce: r.nonce }; };
    const amt = (n: bigint, c = COL_U) => ({ color: c, amount: n, decimals: 0, symbol: 'tU' });
    const o200 = { op: 'withdraw_unshielded_with_grant', amount: amt(200n), recipient: PINNED };
    const ga = await sol.authoriseSolGrantee(G.device, gctx(AU), SITE, o200 as any);
    const gArgs = (au: any, n = 200n, spent = 0n) => [COL_U, n, { bytes: PINNED }, ...grantAuthArgs(opening(spent) as any, au)];
    const ctlG = { a: AU, args: gArgs(ga) };
    const AU2 = await positive('grants', 'the unshielded grantee twin: 200 under the grant; auth_nonce and the device entries untouched', undefined, AU, GWU, ctlG.args,
      (after) => { const l = ledgerOf(after), b = ledgerOf(AU); return l.auth_nonce === b.auth_nonce && l.grants.lookup(G.grantId(after.addressBytes, 0n)).nonce === 1n
        && JSON.stringify([...l.devices].map(hex)) === JSON.stringify([...b.devices].map(hex)); });
    const consG = (au: any, a: LocalAccount, o: any) => ({ ...au, showArgs: sol.solGranteeMessageCircuit(G.key, gctx(a), SITE, o).showArgs });
    await negative('grants', 'grantee binding: the amount changed at execution (consistent display inputs)', AU, GWU, gArgs(consG(ga, AU, { ...o200, amount: amt(201n) }), 201n), GINVALID, [GINVALID], ctlG);
    if (AU2) {
      await negative('grants', 'grantee replay: the landed approval with the current opening and display inputs for the current record nonce', AU2, GWU,
        gArgs(consG(ga, AU2, o200), 200n, 200n), GINVALID, [GINVALID], { a: AU2, args: gArgs(await sol.authoriseSolGrantee(G.device, gctx(AU2), SITE, o200 as any), 200n, 200n) });
    }
    // cross-role (G1S-3): the same key as a device of AX and a grantee of AX
    const wS = sol.solSoftwareSigner(rnd());
    const W = sol.SolEd25519Device.fromSigner(wS, await sol.deriveSolBlind(wS, { network: 'undeployed', accountIndex: 0 }));
    let AX = await activated(W, rnd());
    const WG = await sol.SolEd25519Grantee.enrol(wS, { network: 'undeployed', issuingAccount: AX.addressBytes }, 'Example dApp');
    const sX = scope();
    const saltX = rnd();
    AX = (await execute(Original.Contract, AX, ISSUE, issueArgsOf(WG.grantee(0n), sX, saltX,
      await sol.authoriseSolDevice(W, ctxOf(AX), SITE, { op: 'issue_grant', grantee: WG.grantee(0n), ...sX } as any, 0n)))).after;
    AX = (await execute(Original.Contract, AX, 'deposit_unshielded', [COL_U, 1000n])).after;
    const to = rnd();
    const oX = { op: 'withdraw_unshielded_with_grant', amount: amt(100n), recipient: to };
    const gAuth = await sol.authoriseSolGrantee(WG.device, gctx(AX, 0n, WG), SITE, oX as any);
    const dAuth = await sol.authoriseSolDevice(W, ctxOf(AX), SITE, { op: 'withdraw_unshielded', amount: amt(100n), recipient: to } as any, 1n);
    const xOpen = { originHash: grantOriginHash(msg.labelBytes(WG.label)), slot: 0n, scopeSalt: saltX, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 600n, spentPrev: 0n };
    const ctlX = { a: AX, args: [COL_U, 100n, { bytes: to }, ...grantAuthArgs(xOpen as any, gAuth as any)] };
    await negative('grants', "roles: the same key's device-role approval of the same withdrawal presented to the grant seam", AX, GWU,
      [COL_U, 100n, { bytes: to }, ...grantAuthArgs(xOpen as any, { ...gAuth, sig: dAuth.sig } as any)], GINVALID, [GINVALID], ctlX);
    await negative('grants', "roles: the same key's grantee-role approval presented to the device seam", AX, WU,
      [COL_U, 100n, { bytes: to }, ...authArgs({ ...dAuth, sig: gAuth.sig })], INVALID, [INVALID], { a: AX, args: [COL_U, 100n, { bytes: to }, ...authArgs(dAuth)] });
    await foreignFrameGrantee('grants', rnd, AU, G, gctx(AU), SITE, GWU, o200, (au) => gArgs(au));
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// grantee-scope (G2(S) G2S-1): the three grantee twins at the constraint level
// ═════════════════════════════════════════════════════════════════════════════
async function sectionGranteeScope() {
  const rnd = rng('grantee-scope');
  const SITE = 'Grantee scope prover';
  const { d: S } = await solDevice(rnd());
  const birthG = 0xb1a7c0den;
  // veto window 0, so that a finalisation can run locally
  const A0 = await activated(S, rnd(), birthG, 0n);
  const sSalt = fill(32, 0x5b);
  const issue = async (a: LocalAccount, g: any, sc: any) =>
    (await execute(Original.Contract, a, ISSUE, issueArgsOf(g, sc, sSalt, await sol.authoriseSolDevice(S, ctxOf(a), SITE, { op: 'issue_grant', grantee: g, ...sc } as any, counterIn(a, S))))).after;
  // the grantee G: one key, one grantee blind for this issuing account
  const gSeed = rnd();
  const LABEL = 'bank.example';
  const G = await sol.SolEd25519Grantee.enrol(sol.solSoftwareSigner(gSeed), { network: 'undeployed', issuingAccount: A0.addressBytes }, LABEL);
  const ohG = grantOriginHash(msg.labelBytes(LABEL));
  const rIdentity = rIdentityFor(gSeed, G.key);
  const COLG = fill(32, 0xc7), COLX = fill(32, 0xc8), COL_A = fill(32, 0xa1), COL_B = fill(32, 0xb2);
  const RCPT = fill(32, 0x7e), RCPT2 = fill(32, 0x7f), KEY2 = fill(32, 0x4b), RECIPIENT_CONTRACT = fill(32, 0x3c), CONTRACT2 = fill(32, 0x3d);
  const CALLER_C = fill(32, 0xca), CALLER_W = fill(32, 0xcb);
  const NONCE_H = fill(32, 0x11), NONCE_H2 = fill(32, 0x13), NONCE_OTHER = fill(32, 0x12), FILLER = (i: number) => fill(32, 0xf0 + i);
  const change = fill(192, 0x2c), change2 = fill(192, 0x2d), staleKey = fill(32, 0x5e), readPk = fill(32, 0x77);

  type T = 'U' | 'S' | 'C';
  const CIRCUIT: Record<T, string> = { U: GWU, S: GWS, C: GWSC };
  const TAG: Record<T, string> = { U: 'withdraw_unshielded_with_grant', S: 'withdraw_shielded_with_grant', C: 'withdraw_shielded_to_contract_with_grant' };
  const mainScope = (t: T) => t === 'U'
    ? scopeOf({ opWithdrawUnshielded: true, color: COLG, recipientKind: RECIPIENT_USER_ADDRESS, recipient: RCPT, maxCoinValue: 300n, perCallCap: 300n, cap: 450n })
    : scopeOf({ ...(t === 'S' ? { opWithdrawShielded: true, recipientKind: RECIPIENT_ZSWAP_COIN_PUBLIC_KEY, recipient: localCoinPublicKeyBytes() }
      : { opWithdrawShieldedToContract: true, recipientKind: RECIPIENT_CONTRACT_ADDRESS, recipient: RECIPIENT_CONTRACT }),
      read: true, readPk, color: COL_A, maxCoinValue: 1000n, perCallCap: 500n, cap: 900n });
  // slots: 0 main, 1 max coin 600, 2 caller-pinned, 3 expired, 4 colour B, 5 pinned to another key, 6 the operation not in scope
  const scopes = (t: T) => {
    const m = mainScope(t);
    const notInScope = t === 'U' ? { ...m, opWithdrawUnshielded: false, opWithdrawShielded: true, read: true, readPk }
      : t === 'S' ? { ...m, opWithdrawShielded: false, opWithdrawShieldedToContract: true } : { ...m, opWithdrawShieldedToContract: false, opWithdrawShielded: true };
    return [m, { ...m, maxCoinValue: 600n }, { ...m, caller: CALLER_C }, { ...m, expiresAt: 1n }, { ...m, color: COL_B }, { ...m, recipient: KEY2 }, notInScope];
  };
  const opening = (t: T, slot: bigint, spentPrev = 0n) => {
    const sc = scopes(t)[Number(slot)];
    return { originHash: ohG, slot, scopeSalt: sSalt, recipientKind: sc.recipientKind, pinnedRecipient: sc.recipient, maxCoinValue: sc.maxCoinValue, spentPrev };
  };
  const gctx = (a: LocalAccount, slot: bigint) => { const r = ledgerOf(a).grants.lookup(G.grantId(a.addressBytes, slot)); return { contractAddress: a.addressBytes, label: LABEL, slot, issuedAt: r.issued_at as bigint, grantNonce: r.nonce as bigint }; };
  interface V { amount: bigint; color: Uint8Array; recipient: Uint8Array; coin?: LocalCoin; change: Uint8Array; encPk: Uint8Array }
  interface P { slot?: bigint; amount: bigint; color?: Uint8Array; recipient?: Uint8Array; coin?: LocalCoin; change?: Uint8Array; encPk?: Uint8Array; spentPrev?: bigint; signed?: Partial<V>; ctx?: LocalAccount }
  const opOf = (t: T, v: V) => t === 'U' ? { op: 'withdraw_unshielded_with_grant', amount: { color: v.color, amount: v.amount, decimals: 0, symbol: 'tG' }, recipient: v.recipient }
    : { op: TAG[t], amount: { color: v.color, amount: v.amount, decimals: 0, symbol: 'tG' }, recipient: v.recipient, changeEntry: v.change, encPk: v.encPk,
      coin: { nonce: v.coin!.nonce, color: v.color, value: v.coin!.value, mt_index: v.coin!.mtIndex } };
  /** The twin's arguments with G's approval over the SIGNED values (default: the executed ones). */
  const call = async (t: T, a: LocalAccount, p: P) => {
    const slot = p.slot ?? 0n;
    const sc = scopes(t)[Number(slot)];
    const exec: V = { amount: p.amount, color: p.color ?? (t === 'U' ? COLG : COL_A), recipient: p.recipient ?? sc.recipient, coin: p.coin, change: p.change ?? change, encPk: p.encPk ?? ledgerOf(a).enc_key };
    const ctx = gctx(p.ctx ?? a, slot);
    const ga = await sol.authoriseSolGrantee(G.device, ctx, SITE, opOf(t, exec) as any);
    let auth: any = ga;
    if (p.signed) auth = { ...ga, sig: (await G.device.signBytes(sol.solGranteeMessageCircuit(G.key, ctx, SITE, opOf(t, { ...exec, ...p.signed }) as any).bytes)).sig };
    const o = opening(t, slot, p.spentPrev ?? 0n);
    const args = t === 'U' ? [exec.color, p.amount, { bytes: exec.recipient }, ...grantAuthArgs(o as any, auth)]
      : [{ bytes: exec.recipient }, exec.color, p.amount, exec.change, exec.encPk, ...grantAuthArgs(o as any, auth)];
    return { args, auth: ga };
  };
  const finalised = async (a: LocalAccount) => {
    const l = ledgerOf(a);
    const Q = JubjubDevice.generate();
    const nowUpper = BigInt(Math.floor(Date.now() / 1000)) + 2n;
    const sub = signRecoverSubmit(recoveryKey(birthG), Q,
      recoverSubmitChallenge({ contractAddress: a.addressBytes, authNonce: l.auth_nonce }, l.recovery_pk, Q.pk, recoveryKey(0x9a1n).pk as any, l.device_epoch + 1n, nowUpper),
      { successorRecoveryPk: recoveryKey(0x9a1n).pk as any, expectedEpoch: l.device_epoch, expectedNonce: l.auth_nonce, nowUpper });
    const p = (await execute(Original.Contract, a, 'recover_submit', recoverSubmitArgs(sub))).after;
    await new Promise((r) => setTimeout(r, 3500));
    return (await execute(Original.Contract, p, 'recover_finalise', [])).after;
  };
  const answering = (a: LocalAccount, key: Uint8Array, coin: LocalCoin) => ({ ...a, privateState: coinStoreAnswering([{ key, coin }]) }) as LocalAccount;
  const callerCopyPlain = await copyFor([], CALLER_OVERRIDES);
  for (const t of (process.env.SOL_GRANT_TWINS ?? 'U,S,C').split(',') as T[]) {
    const circuit = CIRCUIT[t], tag = TAG[t];
    console.log(`── ${tag}`);
    let AT = A0;
    const used: Record<T, number[]> = { U: [0, 2, 3, 6], S: [0, 1, 2, 3, 4, 5, 6], C: [0, 1, 2, 3, 4, 6] };
    for (const [i, sc] of scopes(t).entries()) if (used[t].includes(i)) AT = await issue(AT, G.grantee(BigInt(i)), sc);
    const bare = AT;
    let H1: LocalCoin | undefined, H2: LocalCoin | undefined;
    if (t === 'U') { for (const c of [COLG, COLX]) AT = (await execute(Original.Contract, AT, 'deposit_unshielded', [c, 1000n])).after; }
    else {
      const placed = withLocalCoins(AT, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 1000n }, { nonce: NONCE_H2, color: COL_A, value: 1000n }]);
      [, H1, H2] = placed.coins;
      AT = answering(placed.account, COL_A, H1!);
    }
    const honest: P = t === 'U' ? { amount: 200n } : { amount: 300n, coin: H1 };
    const base = { a: AT, args: (await call(t, AT, honest)).args };
    await positive('grantee-scope', `${tag}: the honest call on the base account (original module)`, undefined, AT, circuit, base.args);
    const N = (name: string, a: LocalAccount, args: unknown[], expect: Expect, bypass: string[], opts: NegOpts = {}, control: { a: LocalAccount; args: unknown[] } = base) =>
      negative('grantee-scope', `${tag}: ${name}`, a, circuit, args, expect, bypass, control, opts);

    // ── the scope, each check on its own, under a valid approval ──
    await N("the operation not in the grant's scope (slot 6), honestly signed", AT, (await call(t, AT, { ...honest, slot: 6n })).args, NOT_IN_SCOPE, [NOT_IN_SCOPE]);
    if (t === 'U') {
      await N("the object commitment: a colour the grant does not cover (X, the grant's is G; X in the mirror), honestly signed", AT,
        (await call(t, AT, { ...honest, color: COLX })).args, OBJECT, [OBJECT]);
    } else {
      // the scope's object check on its own: a grant for colour A (slot 0),
      // a coin of colour B withdrawn as B, honestly signed (the colour assert
      // holds: the coin is the withdrawn colour)
      const placed = withLocalCoins(bare, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_B, value: 1000n }]);
      const accB = answering(placed.account, COL_B, placed.coins[1]);
      await N("the object commitment on its own: a grant for colour A, a coin of colour B withdrawn as B, honestly signed (the colour assert holds)", accB,
        (await call(t, accB, { ...honest, color: COL_B, coin: placed.coins[1] })).args, OBJECT, [OBJECT]);
    }
    {
      const pinnedArgs = (await call(t, AT, { ...honest, slot: 2n })).args;
      const noCaller = () => callerInjection.set(undefined), pinned = () => callerInjection.set(CALLER_C), wrong = () => callerInjection.set(CALLER_W);
      const callerCopy = await copyFor([NO_CALLER, CALLER_MISMATCH], CALLER_OVERRIDES);
      await N('the caller pin (slot 2): no contract caller (a root call)', AT, pinnedArgs, NO_CALLER, [NO_CALLER, CALLER_MISMATCH],
        { module: callerCopy, mutant: 'the caller injected into the local call context (CALLER_OVERRIDES): none; control: the pinned contract', hooks: { simulator: noCaller, control: pinned, attempt: noCaller } },
        { a: AT, args: pinnedArgs });
      const mismatchCopy = await copyFor([CALLER_MISMATCH], CALLER_OVERRIDES);
      await N('the caller pin (slot 2): called by another contract', AT, pinnedArgs, CALLER_MISMATCH, [CALLER_MISMATCH],
        { module: mismatchCopy, simulatorModule: callerCopyPlain, mutant: 'the caller injected into the local call context (CALLER_OVERRIDES): another contract; control: the pinned contract', hooks: { simulator: wrong, control: pinned, attempt: wrong } },
        { a: AT, args: pinnedArgs });
      callerInjection.set(undefined);
    }
    await N('over the per-call cap, honestly signed', AT, (await call(t, AT, { ...honest, amount: t === 'U' ? 301n : 501n })).args, PER_CALL, [PER_CALL]);
    await N('a wrong spent opening (spent so far 100, the record holds 0), honestly signed', AT, (await call(t, AT, { ...honest, spentPrev: 100n })).args, SPENT, [SPENT]);
    {
      const first: P = t === 'U' ? { amount: 200n } : { amount: 500n, coin: H1 };
      const A1 = (await execute(Original.Contract, AT, circuit, (await call(t, AT, first)).args)).after;
      const A1n = t === 'U' ? A1 : answering(A1, COL_A, H2!);
      const second: P = t === 'U' ? { amount: 260n, spentPrev: 200n } : { amount: 450n, coin: H2, spentPrev: 500n };
      await N(`over the cumulative cap (${t === 'U' ? '200 + 260 > 450' : '500 + 450 > 900'}), honestly signed with the live spent opening`, A1n, (await call(t, A1n, second)).args, CUMULATIVE, [CUMULATIVE]);
    }
    if (t !== 'U') await N("a coin above the grant's max coin value (1000 > 600, slot 1), honestly signed", AT, (await call(t, AT, { ...honest, slot: 1n })).args, MAX_COIN, [MAX_COIN]);
    else notApplicable('grantee-scope', circuit, `${tag}: the max coin value`, 'the unshielded twin spends from the mirror, not a coin: max_coin_value enters only the object commitment (a changed opening is "scope object mismatch"); the coin bound is the shielded twins\' check_shielded_grant_bounds');
    await N('a recipient other than the pinned one, honestly signed', AT,
      (await call(t, AT, t === 'S' ? { ...honest, slot: 5n, recipient: localCoinPublicKeyBytes() } : { ...honest, recipient: t === 'U' ? RCPT2 : CONTRACT2 })).args, PIN, [PIN]);
    if (t !== 'U') await N('a stale encryption key, honestly signed (the change sealed to a key that is no longer live)', AT, (await call(t, AT, { ...honest, encPk: staleKey })).args, STALE_ENC, [STALE_ENC]);
    else notApplicable('grantee-scope', circuit, `${tag}: a stale encryption key`, 'the unshielded twin produces no change entry and takes no encryption key');

    // ── the record's liveness ──
    const AR = (await execute(Original.Contract, AT, REVOKE, [msg.solGranteeArg(G.grantee(0n)), msg.solTargetPointArg(G.grantee(0n)),
      ...authArgs(await sol.authoriseSolDevice(S, ctxOf(AT), SITE, { op: 'revoke_grant', grantee: G.grantee(0n) } as any, counterIn(AT, S)))])).after;
    await N('a revoked grant (its tombstone), a valid approval over its record', AR, (await call(t, AR, honest)).args, REVOKED, [REVOKED]);
    await N('an expired grant (expires_at 1, slot 3), a valid approval', AT, (await call(t, AT, { ...honest, slot: 3n })).args, EXPIRED, [EXPIRED]);
    const AE = await finalised(AT);
    if (ledgerOf(AE).device_epoch !== 1n || !ledgerOf(AE).grants.member(G.grantId(AE.addressBytes, 0n))) throw new Error('setup: the finalisation did not bump the epoch with the grant kept');
    await N('a grant of a stale device epoch (after a local recover_finalise), a valid approval', AE, (await call(t, AE, honest)).args, EPOCH, [EPOCH]);
    const AX = (await execute(Original.Contract, AT, REVOKE_ALL, authArgs(await sol.authoriseSolDevice(S, ctxOf(AT), SITE, { op: 'revoke_all_grants' } as any, counterIn(AT, S))))).after;
    // the generation cell: the two-level cell whose copy from AX gives generation 1 with the record kept
    let AGN: LocalAccount | undefined, genPath: [number, number] | undefined;
    const top = (AT.state as any).data.state.asArray();
    for (let i = 0; i < top.length && !AGN; i++) {
      const sub = top[i].asArray?.();
      if (!sub) continue;
      for (let j = 0; j < sub.length && !AGN; j++) {
        try {
          const c = withLedgerCell(AT, AX, [i, j]);
          if (ledgerOf(c).grant_generation === 1n && ledgerOf(c).grants.member(G.grantId(c.addressBytes, 0n)) && ledgerOf(c).auth_nonce === ledgerOf(AT).auth_nonce) { AGN = c; genPath = [i, j]; }
        } catch { /* not a copyable cell */ }
      }
    }
    if (!AGN) throw new Error('setup: no ledger cell gives a stale generation with the record kept');
    await N(`a grant of a stale generation — UNREACHABLE today (revoke_all_grants clears the map, account.compact do_revoke_all_grants); the state built by copying the generation cell ${JSON.stringify(genPath)} — a valid approval`,
      AGN, (await call(t, AGN, honest)).args, GEN, [GEN]);
    // an unknown grant id: another blind names an id with no record; the
    // forged grant-id mutant's JavaScript derives the real grant's id from it
    // (so the transcript reads that record), the circuit derives the id from
    // the presented blind
    {
      const forging = await copyFor([], GRANT_ID_FORGE_OVERRIDES);
      const otherBlind = rnd();
      const args = [...base.args]; const last: any = args.at(-1);
      args[args.length - 1] = { ...last, blind: otherBlind };
      const target = { tag: padTag(DESCRIPTOR_TAGS['grant-id'].sol_ed25519), blind: otherBlind, id: G.grantId(AT.addressBytes, 0n) };
      let f0 = 0;
      await N("an unknown grant: another blind (a grant id with no record), the copy's JavaScript deriving the real grant's id from it (forged grant-id mutant)",
        AT, args, UNKNOWN_GRANT, [],
        { module: forging, mutant: 'forged grant-id mutant (persistentHash override) on the grant seam', enforcement: 'constraint', hooks: { control: () => grantIdForgery.set(undefined), attempt: () => { grantIdForgery.set(target); f0 = grantIdForgery.fired; } },
          check: () => (grantIdForgery.fired > f0 ? undefined : 'the grant-id forgery never fired') });
      grantIdForgery.set(undefined);
    }
    await runtimeOnly('grantee-scope', `${tag}: after revoke_all_grants, an approval made before it: the record is absent (the map cleared)`, AX, circuit, (await call(t, AX, { ...honest, ctx: AT })).args, /unknown grant|expected a cell/,
      'revoke_all_grants clears the grants map, so no record exists to read: the generated JavaScript (and the transcript partition the client runs) cannot read one; in-circuit the membership assert refuses it, a constraint on a declared read, and the generation check refuses any copied record (the stale-generation case above)');
    // ── the grant seam ──
    {
      const { auth } = await call(t, AT, honest);
      const args = [...base.args]; const last: any = args.at(-1);
      args[args.length - 1] = { ...last, sig: rIdentity(auth.message) };
      await N('the grant seam: R = O with the verification equation holding (s = k a)', AT, args, RID, [RID]);
    }
    // ── the shielded twins: the coin and the change ──
    if (t !== 'U') {
      const coinH = H1!;
      // the colour assert on its own: a grant scoped to B (slot 4), a valid
      // approval withdrawing A, the witness coin of colour B (the scope's
      // object check holds: its object is the coin's colour, B)
      const colPlaced = withLocalCoins(bare, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_B, value: 1000n }]);
      const colAcc = answering(colPlaced.account, COL_A, colPlaced.coins[1]);
      await N('the colour assert on its own: a grant scoped to B (slot 4), a valid approval withdrawing A, the witness coin of colour B', colAcc,
        (await call(t, colAcc, { ...honest, slot: 4n, coin: colPlaced.coins[1] })).args, COLOUR, [COLOUR]);
      const nonceAcc = answering(withLocalCoins(bare, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_OTHER, color: COL_A, value: 1000n }]).account, COL_A, { ...coinH, nonce: NONCE_OTHER });
      await N("substitution, the coin nonce: signed N, the witness coin N' (same colour, value, index)", nonceAcc,
        (await call(t, nonceAcc, { ...honest, coin: { ...coinH, nonce: NONCE_OTHER }, signed: { coin: coinH } })).args, GINVALID, [GINVALID]);
      const idxPlaced = withLocalCoins(bare, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: FILLER(1), color: COL_A, value: 7n }, { nonce: NONCE_H, color: COL_A, value: 1000n }]);
      const idxAcc = answering(idxPlaced.account, COL_A, idxPlaced.coins[2]);
      await N('substitution, the Merkle index: signed 1, the witness coin at index 2', idxAcc,
        (await call(t, idxAcc, { ...honest, coin: idxPlaced.coins[2], signed: { coin: { ...idxPlaced.coins[2], mtIndex: 1n } } })).args, GINVALID, [GINVALID]);
      await N('substitution, the change entry: signed C1, executed C2', AT, (await call(t, AT, { ...honest, change: change2, signed: { change } })).args, GINVALID, [GINVALID]);
      await N('substitution, the encryption key: signed a stale key, executed with the live key', AT, (await call(t, AT, { ...honest, signed: { encPk: staleKey } })).args, GINVALID, [GINVALID]);
      const valPlaced = withLocalCoins(bare, [{ nonce: FILLER(0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value: 999n }]);
      const valAcc = answering(valPlaced.account, COL_A, valPlaced.coins[1]);
      await N('substitution, the coin value: signed 1000, the witness coin of value 999', valAcc,
        (await call(t, valAcc, { ...honest, coin: valPlaced.coins[1], signed: { coin: { ...valPlaced.coins[1], value: 1000n } } })).args, GINVALID, [GINVALID]);
      await N('substitution, the amount: signed 300, executed 301', AT, (await call(t, AT, { ...honest, amount: 301n, signed: { amount: 300n } })).args, GINVALID, [GINVALID]);
    }
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// frame-lifecycle (G2(S) G2S-4): the foreign-account frame on the remaining
// gated exports
// ═════════════════════════════════════════════════════════════════════════════
async function sectionFrameLifecycle() {
  const rnd = rng('frame-lifecycle');
  const SITE = 'Frame lifecycle prover';
  const { d: S } = await solDevice(rnd());
  const A0 = await activated(S, rnd());
  const jub = JubjubDevice.generate();
  const tJ = sol.solTargetOf({ scheme: 'jubjub', x: jub.pk.x, y: jub.pk.y } as any);
  const IDP = { x: 0n, y: 1n };
  const addArgs = (t: any) => (au: any) => [msg.solTargetArg(t), msg.solTargetPointArg(t), ...authArgs(au)];
  await foreignFrameDevice('frame-lifecycle', rnd, A0, S, SITE, ADD, { op: 'add_device', target: tJ }, addArgs(tJ));
  const A1 = (await execute(Original.Contract, A0, ADD, addArgs(tJ)(await sol.authoriseSolDevice(S, ctxOf(A0), SITE, { op: 'add_device', target: tJ } as any, counterIn(A0, S))))).after;
  const ep = ledgerOf(A1).device_epoch as bigint;
  await foreignFrameDevice('frame-lifecycle', rnd, A1, S, SITE, REMOVE, { op: 'remove_device', literal: false, target: tJ, counter: 0n, epoch: ep },
    (au) => [false, msg.solTargetArg(tJ), msg.solTargetPointArg(tJ), 0n, ep, new Uint8Array(32), ...authArgs(au)], 'remove_device (descriptor form)');
  const eJ = jub.entryAt(A1.addressBytes, ep, 0n);
  await foreignFrameDevice('frame-lifecycle', rnd, A1, S, SITE, REMOVE, { op: 'remove_device', literal: true, entry: eJ },
    (au) => [true, msg.solTargetArg({ tag: '' } as any), IDP, 0n, 0n, eJ, ...authArgs(au)], 'remove_device (literal form)');
  // grants: G is a sol grantee of A0
  const G = await sol.SolEd25519Grantee.enrol(sol.solSoftwareSigner(rnd()), { network: 'undeployed', issuingAccount: A0.addressBytes }, 'Example dApp');
  const COL_A = fill(32, 0xa1);
  const sc = scopeOf({ opWithdrawShielded: true, opWithdrawShieldedToContract: true, read: true, readPk: fill(32, 0x77), color: COL_A, maxCoinValue: 1000n, perCallCap: 600n, cap: 1200n });
  const salt = rnd();
  const g0 = G.grantee(0n);
  await foreignFrameDevice('frame-lifecycle', rnd, A0, S, SITE, ISSUE, { op: 'issue_grant', grantee: g0, ...sc }, (au) => issueArgsOf(g0, sc, salt, au));
  const AG = (await execute(Original.Contract, A0, ISSUE, issueArgsOf(g0, sc, salt, await sol.authoriseSolDevice(S, ctxOf(A0), SITE, { op: 'issue_grant', grantee: g0, ...sc } as any, counterIn(A0, S))))).after;
  await foreignFrameDevice('frame-lifecycle', rnd, AG, S, SITE, REVOKE, { op: 'revoke_grant', grantee: g0 }, (au) => [msg.solGranteeArg(g0), msg.solTargetPointArg(g0), ...authArgs(au)]);
  await foreignFrameDevice('frame-lifecycle', rnd, AG, S, SITE, REVOKE_ALL, { op: 'revoke_all_grants' }, (au) => authArgs(au));
  // the two shielded grantee twins on a local Zswap tree
  const { account, coins } = withLocalCoins(AG, [{ nonce: fill(32, 0xf0), color: COL_A, value: 5n }, { nonce: fill(32, 0x11), color: COL_A, value: 1000n }]);
  const AS = { ...account, privateState: coinStoreAnswering([{ key: COL_A, coin: coins[1] }]) } as LocalAccount;
  const r = ledgerOf(AS).grants.lookup(G.grantId(AS.addressBytes, 0n));
  const ctx = { contractAddress: AS.addressBytes, label: G.label, slot: 0n, issuedAt: r.issued_at as bigint, grantNonce: r.nonce as bigint };
  const enc = ledgerOf(AS).enc_key;
  const chg = fill(192, 0x2c);
  const op = { originHash: grantOriginHash(msg.labelBytes(G.label)), slot: 0n, scopeSalt: salt, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 1000n, spentPrev: 0n };
  for (const [circuit, recipient, opName] of [[GWS, localCoinPublicKeyBytes(), 'withdraw_shielded_with_grant'], [GWSC, fill(32, 0x3c), 'withdraw_shielded_to_contract_with_grant']] as [string, Uint8Array, string][]) {
    const o = { op: opName, amount: { color: COL_A, amount: 300n, decimals: 0, symbol: 'tA' }, recipient, changeEntry: chg, encPk: enc,
      coin: { nonce: coins[1].nonce, color: COL_A, value: 1000n, mt_index: coins[1].mtIndex } };
    await foreignFrameGrantee('frame-lifecycle', rnd, AS, G, ctx, SITE, circuit, o, (au) => [{ bytes: recipient }, COL_A, 300n, chg, enc, ...grantAuthArgs(op as any, au)]);
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// recovery (S9S) and qa-s3 (G1S-6)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionRecovery(doRecovery: boolean, doQaS3: boolean) {
  const rnd = rng('recovery');
  const SITE = 'S9 recovery prover';
  const { seed: sSeed, d: S } = await solDevice(rnd());
  const { d: S2 } = await solDevice(rnd());
  const { d: W } = await solDevice(rnd());
  const { d: stranger } = await solDevice(rnd());
  // window 0 (the constructor's minimum) so that a finalisation can run locally
  const A0 = await activated(S, rnd(), 0xb1a7n, 0n);
  const field = (n: number) => BigInt('0x' + hex(rnd(31))) + BigInt(n);
  const sessionOf = (secret: bigint) => sol.solRecoverySession({ recoveryPk: recoveryKey(secret).pk, sessionNonce: rnd(32), phi: [field(1), field(2)], wrap: rnd(64) } as any);
  type Sess = ReturnType<typeof sessionOf>;
  const sArgs = (x: Sess) => [x.recoveryPk, x.sessionNonce, ...x.phi, x.phiLen, x.wrap];
  const authFor = (a: LocalAccount, d: Dev, o: any, counter = counterIn(a, d)) => sol.authoriseSolDevice(d, ctxOf(a), SITE, o, counter);
  /** Display inputs as the client computes them (renderer values; a non-canonical rendering is possible). */
  const showArgsFor = (a: LocalAccount, d: Dev, o: any, nonce = ledgerOf(a).auth_nonce as bigint, account = a.addressBytes) => {
    const show = msg.solShow(SITE, nonce), frame = msg.solFrameNibbles(account, d.key);
    if (o.op === 'publish_recovery_session') return [msg.digitsOf(o.phiLen, 3), show, frame, msg.nibblesOf(...msg.solDeviceHexValues(o))];
    return [show, frame];
  };
  const bytesFor = (a: LocalAccount, d: Dev, o: any, nonce = ledgerOf(a).auth_nonce as bigint, account = a.addressBytes) =>
    msg.solMessageBytes(msg.solDeviceMessageText({ site: SITE, account, key: d.key, nonce }, o));
  /** The wallet signed `signed`; the call carries display inputs `show`. */
  const signedOver = async (a: LocalAccount, d: Dev, signed: Uint8Array, show: unknown[], counter = counterIn(a, d)) =>
    ({ ...(await authFor(a, d, { op: 'recover_cancel' }, counter)), sig: (await d.signBytes(signed)).sig, showArgs: show });
  const pubArgs = async (a: LocalAccount, x: Sess, d: Dev = S, counter = counterIn(a, d)) => [...sArgs(x), ...authArgs(await authFor(a, d, x, counter))];
  const cancelArgs = async (a: LocalAccount, d: Dev, counter = counterIn(a, d)) => authArgs(await authFor(a, d, { op: 'recover_cancel' }, counter));
  const rIdentity = rIdentityFor(sSeed, S.key);
  const submitArgs = (a: LocalAccount, secret: bigint, successor: any, successorRecoveryPk: any, nowUpper: bigint) => {
    const l = ledgerOf(a);
    const auth = signRecoverSubmit(recoveryKey(secret), successor,
      recoverSubmitChallenge({ contractAddress: a.addressBytes, authNonce: l.auth_nonce }, l.recovery_pk, successor.pk, successorRecoveryPk, l.device_epoch + 1n, nowUpper),
      { successorRecoveryPk, expectedEpoch: l.device_epoch, expectedNonce: l.auth_nonce, nowUpper });
    return recoverSubmitArgs(auth);
  };
  const now = () => BigInt(Math.floor(Date.now() / 1000));

  const S1 = sessionOf(0x5e55n);
  const landed = await pubArgs(A0, S1);
  const A1x = doRecovery ? await positive('recovery', 'publish_recovery_session_with_sol_ed25519: the honest session (1,250-byte approval)', undefined, A0, PUBLISH, landed,
    (after) => { const l = ledgerOf(after); return l.recovery_phi_len === 2n && Buffer.from(l.recovery_session).equals(Buffer.from(S1.sessionNonce)) && l.auth_nonce === 1n; }) : undefined;
  const A1 = A1x ?? (await execute(Original.Contract, A0, PUBLISH, landed)).after;
  const X = sessionOf(0x5e56n);
  const ctlP = { a: A1, args: await pubArgs(A1, X) };

  if (doQaS3) {
    // a non-canonical rendering f + r of each shown Field, signed by the
    // wallet with matching display inputs: only the display check against
    // the canonical cast remains (the Field-to-Bytes<32> rendering is canonical)
    const nc: [string, Sess][] = [
      ['backup vector value 1 shown as f + r', { ...X, phi: [X.phi[0] + FQ, X.phi[1], 0n, 0n] }],
      ['backup vector value 2 shown as f + r', { ...X, phi: [X.phi[0], X.phi[1] + FQ, 0n, 0n] }],
      ['backup vector value 3 (zero) shown as 0 + r', { ...X, phi: [X.phi[0], X.phi[1], FQ, 0n] }],
      ["the recovery key's x shown as x + r", { ...X, recoveryPk: { ...X.recoveryPk, x: X.recoveryPk.x + FQ } }],
      ["the recovery key's y shown as y + r", { ...X, recoveryPk: { ...X.recoveryPk, y: X.recoveryPk.y + FQ } }],
    ] as any;
    for (const [name, shown] of nc) {
      await negative('qa-s3', `${name} (the executed value is f; the wallet signed the non-canonical rendering)`, A1, PUBLISH,
        [...sArgs(X), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, shown), showArgsFor(A1, S, shown)))], HEXD, [HEXD], ctlP);
    }
  }
  if (!doRecovery) return;

  const other = recoveryKey(0x0dd0n).pk;
  const flip = (b: Uint8Array, i: number) => { const o = new Uint8Array(b); o[i] ^= 1; return o; };
  const variants: [string, Sess][] = [
    ['the recovery key', { ...X, recoveryPk: other }],
    ['the session identifier', { ...X, sessionNonce: flip(X.sessionNonce, 31) }],
    ['backup vector value 1', { ...X, phi: [X.phi[0] + 1n, X.phi[1], 0n, 0n] }],
    ['backup vector value 2', { ...X, phi: [X.phi[0], X.phi[1] + 1n, 0n, 0n] }],
    ['backup vector value 3 (an unused slot) and the length', { ...X, phi: [X.phi[0], X.phi[1], 7n, 0n], phiLen: 3n }],
    ['the length (3, slot 3 zero)', { ...X, phiLen: 3n }],
    ['the wrap', { ...X, wrap: flip(X.wrap, 63) }],
  ] as any;
  for (const [name, Y] of variants) {
    await negative('recovery', `publish binding: ${name} — the wallet signed the session, the call executes another value`, A1, PUBLISH,
      [...sArgs(Y), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, X), showArgsFor(A1, S, Y)))], INVALID, [INVALID], ctlP);
  }
  await negative('recovery', 'publish binding: the nonce — the approval shows auth_nonce + 1', A1, PUBLISH,
    [...sArgs(X), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, X, ledgerOf(A1).auth_nonce + 1n), showArgsFor(A1, S, X)))], INVALID, [INVALID], ctlP);
  await negative('recovery', 'publish operation: a recover_cancel approval presented as the session approval', A1, PUBLISH,
    [...sArgs(X), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, { op: 'recover_cancel' }), showArgsFor(A1, S, X)))], INVALID, [INVALID], ctlP);
  {
    const acct = rnd();
    await negative('recovery', 'publish: the seam owns the frame — the wallet signed the session showing a foreign account (its frame nibbles with it)', A1, PUBLISH,
      [...sArgs(X), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, X, ledgerOf(A1).auth_nonce, acct), showArgsFor(A1, S, X, ledgerOf(A1).auth_nonce, acct)))], HEXD, [HEXD], ctlP);
  }
  const aX = await authFor(A1, S, X);
  {
    const Y = { ...X, phi: [X.phi[0] + 1n, X.phi[1], 0n, 0n] } as Sess;
    await negative('recovery', "publish display: the hex nibbles and the signed message show another backup vector value 1; the call executes the session's", A1, PUBLISH,
      [...sArgs(X), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, Y), showArgsFor(A1, S, Y)))], HEXD, [HEXD], ctlP);
  }
  {
    const Y = { ...X, phi: [X.phi[0], X.phi[1], 5n, 0n], phiLen: 3n } as Sess;
    const Z = { ...Y, phiLen: 2n } as Sess;
    await negative('recovery', 'publish display: the length digits and the signed message show 2, the call executes 3 (hex nibbles consistent)', A1, PUBLISH,
      [...sArgs(Y), ...authArgs(await signedOver(A1, S, bytesFor(A1, S, Z), showArgsFor(A1, S, Z)))], DIGITS, [DIGITS], ctlP);
  }
  const chip: [string, Sess, string, string[]][] = [
    ['an empty vector (length 0)', { ...X, phi: [0n, 0n, 0n, 0n], phiLen: 0n }, EMPTY, [EMPTY]],
    ['a length beyond the slot bound (5)', { ...X, phi: [1n, 2n, 3n, 4n], phiLen: 5n }, RANGE, [RANGE]],
    ['length 1 with slot 2 non-zero', { ...X, phi: [1n, 2n, 0n, 0n], phiLen: 1n }, SLOT2, [SLOT2]],
    ['length 2 with slot 3 non-zero', { ...X, phi: [1n, 2n, 3n, 0n], phiLen: 2n }, SLOT3, [SLOT3]],
    ['length 3 with slot 4 non-zero', { ...X, phi: [1n, 2n, 3n, 4n], phiLen: 3n }, SLOT4, [SLOT4]],
    ['an all-zero session identifier', { ...X, sessionNonce: new Uint8Array(32) }, SIDZERO, [SIDZERO]],
    ['the stored session identifier reused', { ...X, sessionNonce: new Uint8Array(S1.sessionNonce) }, SIDREUSE, [SIDREUSE]],
    ['the stored recovery commitment reused', { ...X, recoveryPk: S1.recoveryPk }, PKREUSE, [PKREUSE]],
    ['the identity as the new recovery key', { ...X, recoveryPk: JUBJUB_IDENTITY }, IDENT, [IDENT, SMALL]],
  ] as any;
  for (const [name, x, expect, bypass] of chip) await negative('recovery', `chip: publish under a valid signature, ${name}`, A1, PUBLISH, await pubArgs(A1, x), expect, bypass, ctlP);
  {
    // a torsion point traps in the runtime's JubJub code before the circuit body
    const name = 'chip: publish under a valid signature, a small-order recovery key (runtime trap)';
    const r: Result = { section: 'recovery', circuit: PUBLISH, case: name, kind: 'negative', expect: 'unreachable' };
    const chain: string[] = [];
    let refusedT = false;
    try { await execute(Original.Contract, A1, PUBLISH, await pubArgs(A1, { ...X, recoveryPk: JUBJUB_ORDER_TWO } as Sess)); }
    catch (e: any) { refusedT = true; for (let x = e; x; x = x.cause) chain.push(`${x.name}: ${x.message}`); }
    const trap = refusedT && chain.some((m) => /unreachable|small order/.test(m));
    r.simulator = { verdict: trap ? 'PASS' : refusedT ? 'ERROR' : 'FAIL', layer: 'runtime', reason: trap ? 'refused by the runtime (JubJub point handling) before the circuit body' : 'not refused as expected', detail: chain.join(' | ').slice(0, 600) } as any;
    r.proverLevel = 'not reachable from a JavaScript-built call: the runtime cannot construct a JubJub point outside the prime-order subgroup, and the proving toolchain constrains every assigned point into the subgroup (upstream recovery-sim; require_live_jubjub_point is defence in depth)';
    tally(r.simulator); results.push(r); line(r);
  }
  await negative('recovery', 'seam: publish, an unenrolled sol key signs the session', A1, PUBLISH, await pubArgs(A1, X, stranger, 0n), UNKNOWN, [UNKNOWN], ctlP);
  await negative('recovery', 'seam: publish, the device key with another blind', A1, PUBLISH, [...sArgs(X), ...authArgs({ ...aX, blind: rnd() })], UNKNOWN, [UNKNOWN], ctlP);
  await negative('recovery', 'seam: publish, a stale use counter (counter 0, already rolled)', A1, PUBLISH, await pubArgs(A1, X, S, 0n), UNKNOWN, [UNKNOWN], ctlP);
  await negative('recovery', 'seam: publish, R = O with the verification equation holding (s = k a)', A1, PUBLISH, [...sArgs(X), ...authArgs({ ...aX, sig: rIdentity(aX.message) })], RID, [RID], ctlP);
  await negative('recovery', 'replay: publish, the landed session approval replayed with display inputs for the current nonce (entry consumed, stored values)', A1, PUBLISH,
    [...sArgs(S1), ...authArgs({ ...(await authFor(A0, S, S1, 0n)), showArgs: showArgsFor(A1, S, S1) })], UNKNOWN, [UNKNOWN, INVALID, SIDREUSE, PKREUSE], ctlP);

  // a pending recovery: S adds S2 (sol) and J (jubjub) by descriptor, J plants W at epoch + 1
  const jub = JubjubDevice.generate();
  let AD = A1;
  for (const d of [S2.descriptor(), { scheme: 'jubjub', x: jub.pk.x, y: jub.pk.y }]) {
    const t = sol.solTargetOf(d as any);
    AD = (await execute(Original.Contract, AD, ADD, [msg.solTargetArg(t), msg.solTargetPointArg(t), ...authArgs(await authFor(AD, S, { op: 'add_device', target: t }))])).after;
  }
  const plant = W.entryAt(AD.addressBytes, 1n, 0n);
  const AW = (await execute(Original.Contract, AD, 'add_device_with_jubjub', [plant, ...authArgs(jub.sign(jubjubChallenges.addDevice(ctxOf(AD), jub.pk, plant), 0n))])).after;
  if (!ledgerOf(AW).devices.member(plant) || ledgerOf(AW).device_count !== 4n) throw new Error('setup: the plant did not land');
  const Q = JubjubDevice.generate();
  const QR = 0x9e11n;
  const AP = (await execute(Original.Contract, AW, 'recover_submit', submitArgs(AW, 0x5e55n, Q, recoveryKey(QR).pk, now() + 2n))).after;
  if (!ledgerOf(AP).pending_recovery) throw new Error('setup: the submission did not land');
  await negative('recovery', 'chip: publish under a valid signature while a recovery is pending', AP, PUBLISH, await pubArgs(AP, X), PENDING, [PENDING], ctlP);

  const C = { op: 'recover_cancel' };
  const cancelHonest = await cancelArgs(AP, S2);
  const ctlC = { a: AP, args: cancelHonest };
  const ACx = await positive('recovery', 'recover_cancel_with_sol_ed25519: the second sol device vetoes the pending recovery (391-byte approval)', undefined, AP, CANCEL, cancelHonest,
    (after) => ledgerOf(after).pending_recovery === false && ledgerOf(after).auth_nonce === ledgerOf(AP).auth_nonce + 1n);
  const AC = ACx ?? (await execute(Original.Contract, AP, CANCEL, cancelHonest)).after;
  await negative('recovery', 'cancel operation: a revoke_all_grants approval over the same frame presented as the cancel', AP, CANCEL,
    authArgs(await signedOver(AP, S2, bytesFor(AP, S2, { op: 'revoke_all_grants' }), showArgsFor(AP, S2, C))), INVALID, [INVALID], ctlC);
  await negative('recovery', 'cancel binding: the approval shows auth_nonce + 1', AP, CANCEL,
    authArgs(await signedOver(AP, S2, bytesFor(AP, S2, C, ledgerOf(AP).auth_nonce + 1n), showArgsFor(AP, S2, C))), INVALID, [INVALID], ctlC);
  await negative('recovery', "cancel binding: the approval shows another account (this account's frame nibbles)", AP, CANCEL,
    authArgs(await signedOver(AP, S2, bytesFor(AP, S2, C, ledgerOf(AP).auth_nonce, rnd()), showArgsFor(AP, S2, C))), INVALID, [INVALID], ctlC);
  {
    const acct = rnd();
    await negative('recovery', 'cancel: the seam owns the frame — the wallet signed a cancel showing a foreign account (its frame nibbles with it)', AP, CANCEL,
      authArgs(await signedOver(AP, S2, bytesFor(AP, S2, C, ledgerOf(AP).auth_nonce, acct), showArgsFor(AP, S2, C, ledgerOf(AP).auth_nonce, acct))), HEXD, [HEXD], ctlC);
  }
  await negative('recovery', 'cancel display: the nonce digits and the signed message show auth_nonce + 1', AP, CANCEL,
    authArgs(await signedOver(AP, S2, bytesFor(AP, S2, C, ledgerOf(AP).auth_nonce + 1n), showArgsFor(AP, S2, C, ledgerOf(AP).auth_nonce + 1n))), DIGITS, [DIGITS], ctlC);
  await negative('recovery', 'seam: cancel, an unenrolled sol key', AP, CANCEL, await cancelArgs(AP, stranger, 0n), UNKNOWN, [UNKNOWN], ctlC);
  {
    const a = await authFor(AP, S, C);
    await negative('recovery', 'seam: cancel, R = O with the verification equation holding (s = k a)', AP, CANCEL, authArgs({ ...a, sig: rIdentity(a.message) }), RID, [RID], ctlC);
  }
  await negative('recovery', 'chip: a valid cancel with nothing pending', A1, CANCEL, await cancelArgs(A1, S), NOPENDING, [NOPENDING], ctlC);
  await negative('recovery', 'replay: cancel, the landed cancel replayed with display inputs for the current nonce (entry consumed, nothing pending)', AC, CANCEL,
    authArgs({ ...(await authFor(AP, S2, C, 0n)), showArgs: showArgsFor(AC, S2, C) }), UNKNOWN, [UNKNOWN, INVALID, NOPENDING], ctlC);

  // finalisation (#183)
  const AP2 = (await execute(Original.Contract, AC, 'recover_submit', submitArgs(AC, 0x5e55n, Q, recoveryKey(QR).pk, now() + 2n))).after;
  const lastS = counterIn(AP2, S), lastS2 = counterIn(AP2, S2);
  await new Promise((r) => setTimeout(r, 3500));
  const AF0 = (await execute(Original.Contract, AP2, 'recover_finalise', [])).after;
  const lf = ledgerOf(AF0);
  stateOnly('recovery', "finalised: the set holds only the successor; the plant is W's entry at the new epoch and is gone",
    lf.devices.size() === 1n && lf.device_epoch === 1n && !lf.devices.member(plant) && Buffer.from(plant).equals(Buffer.from(W.entryAt(AF0.addressBytes, lf.device_epoch, 0n))));
  const { d: F } = await solDevice(rnd());
  const fEntry = F.entryAt(AF0.addressBytes, lf.device_epoch, 0n);
  const AF = (await execute(Original.Contract, AF0, 'add_device_with_jubjub', [fEntry, ...authArgs(Q.sign(jubjubChallenges.addDevice(ctxOf(AF0), Q.pk, fEntry), 0n))])).after;
  const S3 = sessionOf(0x5e57n);
  await positive('recovery', 'after the recovery: a fresh sol device enrolled by the successor publishes a session', undefined, AF, PUBLISH, await pubArgs(AF, S3, F),
    (after) => Buffer.from(ledgerOf(after).recovery_session).equals(Buffer.from(S3.sessionNonce)));
  const AFP = (await execute(Original.Contract, AF, 'recover_submit', submitArgs(AF, QR, JubjubDevice.generate(), recoveryKey(0x9e12n).pk, now() + 600n))).after;
  await positive('recovery', 'after the recovery: the fresh sol device cancels a new pending recovery', undefined, AFP, CANCEL, await cancelArgs(AFP, F),
    (after) => ledgerOf(after).pending_recovery === false);
  const ctlF = { a: AF, args: await pubArgs(AF, S3, F) };
  const ctlFC = { a: AFP, args: await cancelArgs(AFP, F) };
  for (const [name, d, c] of [["the planted entry's device W (counter 0 at the new epoch)", W, 0n], [`the original device S (its last counter ${lastS})`, S, lastS], [`the second sol device S2 (its last counter ${lastS2})`, S2, lastS2]] as const) {
    await negative('recovery', `after the recovery: ${name} publishes`, AF, PUBLISH, await pubArgs(AF, S3, d, c), UNKNOWN, [UNKNOWN], ctlF);
    await negative('recovery', `after the recovery: ${name} cancels a pending recovery`, AFP, CANCEL, await cancelArgs(AFP, d, c), UNKNOWN, [UNKNOWN], ctlFC);
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// readability (Q43 words; Q44 = A″: every number in full digits)
// ═════════════════════════════════════════════════════════════════════════════
async function sectionReadability() {
  const rnd = rng('readability');
  const SITE = 'S9 Q43 prover';
  const { d: S } = await solDevice(rnd());
  const A0 = await activated(S, rnd());
  const authFor = (a: LocalAccount, o: any) => sol.authoriseSolDevice(S, ctxOf(a), SITE, o, counterIn(a, S));
  /** The honest text with `from` replaced by `to` (exactly once, same length), as bytes the wallet signs. */
  const forge = (text: string, from: string, to: string) => {
    if (text.split(from).length !== 2) throw new Error(`forge: "${from}" not found exactly once`);
    if (from.length !== to.length) throw new Error('forge: the forged text must keep the layout');
    return msg.solMessageBytes(text.replace(from, to));
  };
  const forgedAuth = async (honest: any, from: string, to: string, dev: any = S) => ({ ...honest, sig: (await dev.signBytes(forge(honest.text, from, to))).sig });
  const d39 = (v: bigint | string) => String(v).padEnd(39, ' ');
  const amt = (color: Uint8Array, amount: bigint, decimals = 0, symbol = 'tTOK') => ({ color, amount, decimals, symbol });
  // custody
  const COL_U = fill(32, 0xc1), RU = fill(32, 0x77);
  const AU = (await execute(Original.Contract, A0, 'deposit_unshielded', [COL_U, 5_000_000n])).after;
  const oU = { op: 'withdraw_unshielded', amount: amt(COL_U, 1_000_000n, 6, 'tUSDC'), recipient: RU };
  const aU = await authFor(AU, oU);
  const uArgs = (au: any) => [COL_U, 1_000_000n, { bytes: RU }, ...authArgs(au)];
  const ctlU = { a: AU, args: uArgs(aU) };
  textCheck('readability', 'withdraw_unshielded: "Amount (base units): 1000000…" in full digits, no magnitude (620 bytes)', aU.message.length === 620 && aU.text.includes(`Amount (base units): ${d39(1_000_000n)}\n`) && !aU.text.includes(' x 10^'));
  await positive('readability', 'withdraw_unshielded 10^6: proved', undefined, AU, WU, ctlU.args);
  await negative('readability', 'forged amount: the wallet signed "100000" for an executed 1000000', AU, WU, uArgs(await forgedAuth(aU, `Amount (base units): ${d39(1_000_000n)}`, `Amount (base units): ${d39(100_000n)}`)), INVALID, [INVALID], ctlU);
  for (const [name, units, expect] of [
    ['forged digits: a leading zero', '01000000', LEADING],
    ['forged digits: a digit after the padding', '1000000 0', ALIGN],
  ] as const) {
    const copy = await copyFor([expect]);
    const shown = [...aU.showArgs] as any[];
    shown[0] = { ...shown[0], units: [...Buffer.from(units.padEnd(39, ' '), 'ascii')].map(BigInt) };
    const bytes: Uint8Array = copy.pureCircuits.sol_message_withdraw_unshielded({ bytes: AU.addressBytes }, S.key, ledgerOf(AU).auth_nonce, COL_U, 1_000_000n, { bytes: RU }, ...shown);
    const { sig } = await S.signBytes(bytes);
    await negative('readability', `${name}, signed over what they render`, AU, WU, uArgs({ ...aU, sig, showArgs: shown }), expect, [expect], ctlU);
  }
  const COL_A = fill(32, 0xa1), NONCE_H = fill(32, 0x11), RC = fill(32, 0x3c);
  const shieldedAccount = (base: LocalAccount, value: bigint) => {
    const { account, coins } = withLocalCoins(base, [{ nonce: fill(32, 0xf0), color: COL_A, value: 5n }, { nonce: NONCE_H, color: COL_A, value }]);
    return { a: { ...account, privateState: coinStoreAnswering([{ key: COL_A, coin: coins[1] }]) } as LocalAccount, coin: coins[1] };
  };
  for (const circuit of [WS, WSC]) {
    const H = shieldedAccount(A0, 1000n);
    const recipient = circuit === WS ? localCoinPublicKeyBytes() : RC;
    const o = { op: circuit === WS ? 'withdraw_shielded' : 'withdraw_shielded_to_contract', amount: amt(COL_A, 300n), recipient,
      coin: { nonce: H.coin.nonce, color: COL_A, value: 1000n, mt_index: H.coin.mtIndex } };
    const au = await authFor(H.a, o);
    const sArgs = (x: any) => [{ bytes: recipient }, COL_A, 300n, ...authArgs(x)];
    const short = circuit === WS ? 'withdraw_shielded' : 'withdraw_shielded_to_contract';
    const len = circuit === WS ? 861 : 871;
    textCheck('readability', `${short}: the amount, the spent value and the change in full digits (${len} bytes)`, au.message.length === len
      && au.text.includes(`Spent coin value: ${d39(1000n)}\n`) && au.text.includes(`Change back to this account: ${d39(700n)}\n`) && au.text.includes(`Amount (base units): ${d39(300n)}\n`));
    await positive('readability', `${short} 300 of a 1000 coin: proved`, undefined, H.a, circuit, sArgs(au));
    if (circuit === WS) await negative('readability', 'forged change: the wallet signed the change as 70', H.a, circuit,
      sArgs(await forgedAuth(au, `Change back to this account: ${d39(700n)}`, `Change back to this account: ${d39(70n)}`)), INVALID, [INVALID], { a: H.a, args: sArgs(au) });
  }
  // devices: a passkey target shows its RP hash in hex (Q46: never a word)
  const pass = softwarePasskey();
  const tR = sol.solTargetOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y, policy: { rpIdHash: pass.policy.rp_id_hash, origin: pass.policy.origin } } as any);
  const aR = await authFor(A0, { op: 'add_device', target: tR });
  const addArgs = (t: any, x: any) => [msg.solTargetArg(t), msg.solTargetPointArg(t), ...authArgs(x)];
  const ctlAdd = { a: A0, args: addArgs(tR, aR) };
  const NA = 'not applicable'.padEnd(64, ' ');
  textCheck('readability', 'add_device: a passkey target shows its RP hash as 64 hex digits (705 bytes)', aR.message.length === 705 && aR.text.includes(`Passkey RP (hash): ${hex(pass.policy.rp_id_hash)}\n`));
  const A1 = await positive('readability', 'add_device of that passkey target: proved', undefined, A0, ADD, ctlAdd.args);
  await negative('readability', 'forged word: the wallet signed "not applicable" for a passkey target\'s RP hash', A0, ADD,
    addArgs(tR, await forgedAuth(aR, `Passkey RP (hash): ${hex(pass.policy.rp_id_hash)}`, `Passkey RP (hash): ${NA}`)), INVALID, [INVALID], ctlAdd);
  const A1x = A1 ?? (await execute(Original.Contract, A0, ADD, ctlAdd.args)).after;
  {
    const o = { op: 'remove_device', literal: false, target: tR, counter: 0n, epoch: ledgerOf(A1x).device_epoch as bigint };
    const au = await authFor(A1x, o);
    await positive('readability', 'remove_device of that passkey target by descriptor (its RP hash in hex in the removal\'s block): proved', undefined, A1x, REMOVE,
      [false, msg.solTargetArg(tR), msg.solTargetPointArg(tR), 0n, o.epoch, Z32, ...authArgs(au)], (after) => ledgerOf(after).device_count === 1n);
  }
  // grants
  const G = await sol.SolEd25519Grantee.enrol(sol.solSoftwareSigner(rnd()), { network: 'undeployed', issuingAccount: A0.addressBytes }, 'Example dApp');
  const scope = (o: any = {}) => scopeOf({ opWithdrawUnshielded: true, color: COL_U, maxCoinValue: MAX128, perCallCap: MAX128, cap: MAX128, ...o });
  const sG = scope();
  const saltG = rnd();
  const gG = G.grantee(0n);
  const aI = await authFor(A0, { op: 'issue_grant', grantee: gG, ...sG });
  const ctlI = { a: A0, args: issueArgsOf(gG, sG, saltG, aI) };
  const MAXTXT = d39(MAX128);
  textCheck('readability', 'issue_grant: caps of 2^128 - 1 in full digits, expiry 0 reads "never", a non-passkey grantee\'s zero RP hash "not applicable" (1,662 bytes)',
    aI.message.length === 1662 && aI.text.includes(`Total cap: ${MAXTXT}\n`) && aI.text.includes(`Max coin value: ${MAXTXT}\n`) && aI.text.includes(`Per-call cap: ${MAXTXT}\n`)
    && aI.text.includes(`Expires at (block time, seconds): ${'never'.padEnd(20)}\n`) && aI.text.includes(`Passkey RP (hash): ${NA}\n`) && aI.text.includes(`Window cap: ${d39(0n)}\n`) && !aI.text.includes(' x 10^'));
  const AG = await positive('readability', 'issue_grant to a sol grantee with the words and the full digits: proved', undefined, A0, ISSUE, ctlI.args, (after) => ledgerOf(after).grants.member(G.grantId(after.addressBytes, 0n)));
  await negative('readability', 'forged cap: the wallet signed "no limit" for the total cap', A0, ISSUE, issueArgsOf(gG, sG, saltG, await forgedAuth(aI, `Total cap: ${MAXTXT}`, `Total cap: ${d39('no limit')}`)), INVALID, [INVALID], ctlI);
  await negative('readability', 'forged word: the wallet signed "0" instead of "never" for an expiry of 0', A0, ISSUE, issueArgsOf(gG, sG, saltG, await forgedAuth(aI, `seconds): ${'never'.padEnd(20)}`, `seconds): ${'0'.padEnd(20)}`)), INVALID, [INVALID], ctlI);
  await negative('readability', 'forged word: the wallet signed 64 zeros for a non-passkey grantee\'s zero RP hash', A0, ISSUE, issueArgsOf(gG, sG, saltG, await forgedAuth(aI, `Passkey RP (hash): ${NA}`, `Passkey RP (hash): ${'0'.repeat(64)}`)), INVALID, [INVALID], ctlI);
  {
    const gP = sol.solGranteeOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y } as any, { origin: pass.policy.origin }, 0n);
    const sP = scope({ opWithdrawUnshielded: false, read: true, readPk: rnd(), rpIdHash: pass.policy.rp_id_hash, color: Z32, maxCoinValue: 0n, perCallCap: 0n, cap: 0n, expiresAt: 1_000n });
    const saltP = rnd();
    const aP = await authFor(A0, { op: 'issue_grant', grantee: gP, ...sP });
    textCheck('readability', 'issue_grant to a passkey grantee: the RP hash in hex, the expiry in seconds, zero caps read "0"',
      aP.text.includes(`Passkey RP (hash): ${hex(pass.policy.rp_id_hash)}\n`) && aP.text.includes(`Expires at (block time, seconds): ${'1000'.padEnd(20)}\n`) && aP.text.includes(`Total cap: ${d39(0n)}\n`));
    await positive('readability', 'issue_grant to a passkey grantee (RP hash, expiry 1000): proved', undefined, A0, ISSUE, issueArgsOf(gP, sP, saltP, aP));
    const ctlP = { a: A0, args: issueArgsOf(gP, sP, saltP, aP) };
    await negative('readability', 'forged word: the wallet signed "never" for an expiry of 1000', A0, ISSUE, issueArgsOf(gP, sP, saltP, await forgedAuth(aP, `seconds): ${'1000'.padEnd(20)}`, `seconds): ${'never'.padEnd(20)}`)), INVALID, [INVALID], ctlP);
    await negative('readability', 'forged word: the wallet signed "not applicable" for a passkey grantee\'s RP hash', A0, ISSUE, issueArgsOf(gP, sP, saltP, await forgedAuth(aP, `Passkey RP (hash): ${hex(pass.policy.rp_id_hash)}`, `Passkey RP (hash): ${NA}`)), INVALID, [INVALID], ctlP);
  }
  // the grantee twins
  const AGx = AG ?? (await execute(Original.Contract, A0, ISSUE, ctlI.args)).after;
  const AGU = (await execute(Original.Contract, AGx, 'deposit_unshielded', [COL_U, 5_000_000n])).after;
  const opening = (slot: bigint, s: Uint8Array, spent: bigint, maxCoin: bigint) => ({ originHash: grantOriginHash(msg.labelBytes(G.label)), slot, scopeSalt: s, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: maxCoin, spentPrev: spent });
  const gctx = (a: LocalAccount, slot: bigint) => { const r = ledgerOf(a).grants.lookup(G.grantId(a.addressBytes, slot)); return { contractAddress: a.addressBytes, label: G.label, slot, issuedAt: r.issued_at, grantNonce: r.nonce }; };
  {
    const o = { op: 'withdraw_unshielded_with_grant', amount: amt(COL_U, 2_500_000n), recipient: RU };
    const ga = await sol.authoriseSolGrantee(G.device, gctx(AGU, 0n), SITE, o as any);
    const gArgs = (x: any) => [COL_U, 2_500_000n, { bytes: RU }, ...grantAuthArgs(opening(0n, saltG, 0n, MAX128) as any, x)];
    const ctlG = { a: AGU, args: gArgs(ga) };
    textCheck('readability', 'the unshielded twin: "Amount (base units): 2500000…" in full digits (746 bytes)', ga.message.length === 746 && ga.text.includes(`Amount (base units): ${d39(2_500_000n)}\n`));
    await positive('readability', 'the unshielded twin: proved; auth_nonce untouched', undefined, AGU, GWU, ctlG.args, (after) => ledgerOf(after).auth_nonce === ledgerOf(AGU).auth_nonce);
    await negative('readability', 'forged amount: the grantee signed "250000" for an executed 2500000', AGU, GWU, gArgs(await forgedAuth(ga, `Amount (base units): ${d39(2_500_000n)}`, `Amount (base units): ${d39(250_000n)}`, G.device)), GINVALID, [GINVALID], ctlG);
  }
  {
    const sS = scope({ opWithdrawUnshielded: false, opWithdrawShielded: true, opWithdrawShieldedToContract: true, read: true, readPk: rnd(), color: COL_A, maxCoinValue: 1000n, perCallCap: 600n, cap: 600n });
    const saltS = rnd();
    const AS = (await execute(Original.Contract, A0, ISSUE, issueArgsOf(G.grantee(1n), sS, saltS, await authFor(A0, { op: 'issue_grant', grantee: G.grantee(1n), ...sS })))).after;
    for (const circuit of [GWS, GWSC]) {
      const H = shieldedAccount(AS, 1000n);
      const enc = ledgerOf(H.a).enc_key;
      const change = rnd(192);
      const recipient = circuit === GWS ? localCoinPublicKeyBytes() : RC;
      const o = { op: circuit === GWS ? 'withdraw_shielded_with_grant' : 'withdraw_shielded_to_contract_with_grant', amount: amt(COL_A, 300n), recipient, changeEntry: change, encPk: enc,
        coin: { nonce: H.coin.nonce, color: COL_A, value: 1000n, mt_index: H.coin.mtIndex } };
      const ga = await sol.authoriseSolGrantee(G.device, gctx(H.a, 1n), SITE, o as any);
      const len = circuit === GWS ? 1586 : 1596;
      textCheck('readability', `the ${circuit === GWS ? 'shielded' : 'to-contract'} twin: the amount, spent value and change in full digits (${len} bytes)`, ga.message.length === len
        && ga.text.includes(`Spent coin value: ${d39(1000n)}\n`) && ga.text.includes(`Change back to this account: ${d39(700n)}\n`));
      await positive('readability', `the ${circuit === GWS ? 'shielded' : 'to-contract'} twin 300 of a 1000 coin: proved`, undefined, H.a, circuit,
        [{ bytes: recipient }, COL_A, 300n, change, enc, ...grantAuthArgs(opening(1n, saltS, 0n, 1000n) as any, ga)]);
    }
  }
}

// ═════════════════════════════════════════════════════════════════════════════
// rules (Q46 = A, Q47 = A): a passkey's own RP hash is never zero; an
// any-recipient grant carries no recipient
// ═════════════════════════════════════════════════════════════════════════════
async function sectionRules() {
  const rnd = rng('rules');
  const SITE = 'Q46 Q47 prover';
  const { d: S } = await solDevice(rnd());
  const A0 = await activated(S, rnd());
  const authFor = (a: LocalAccount, o: any) => sol.authoriseSolDevice(S, ctxOf(a), SITE, o, counterIn(a, S));
  /** A valid signature over the CONTRACT's own bytes (the client renderer
   *  refuses these values, so the bytes come from the pure message circuit). */
  const circuitAuth = async (a: LocalAccount, o: any) => {
    const { bytes, showArgs } = sol.solDeviceMessageCircuit(S.key, ctxOf(a), SITE, o);
    return { ...(await authFor(a, { op: 'revoke_all_grants' })), sig: (await S.signBytes(bytes)).sig, showArgs, message: bytes };
  };
  const ZERO_PK = "descriptor: a passkey's RP hash is zero";
  const ZERO_GRANTEE = "sol_ed25519: a passkey grantee's RP hash is zero";
  const RECIPIENT = 'sol_ed25519: a recipient without a recipient kind';
  const pass = softwarePasskey();
  const tR = sol.solTargetOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y, policy: { rpIdHash: pass.policy.rp_id_hash, origin: pass.policy.origin } } as any);
  const tZ = { ...tR, c: new Uint8Array(32) };
  const addArgs = (t: any, x: any) => [msg.solTargetArg(t), msg.solTargetPointArg(t), ...authArgs(x)];
  const ctlAdd = { a: A0, args: addArgs(tR, await authFor(A0, { op: 'add_device', target: tR })) };
  await negative('rules', 'Q46: add_device of a passkey target whose RP hash is zero, under a valid signature over the contract\'s bytes', A0, ADD,
    addArgs(tZ, await circuitAuth(A0, { op: 'add_device', target: tZ })), ZERO_PK, [ZERO_PK], ctlAdd);
  // remove_device by descriptor: the zero-hash passkey's entry planted
  // through an upstream arm's raw add_device (the w117 recipe, recomputed)
  const k1 = K256Device.generate();
  const A1 = (await execute(Original.Contract, A0, ADD, addArgs(sol.solTargetOf({ scheme: 'k256', x: k1.pk.x, y: k1.pk.y, envelope: Number(k1.envelope) } as any),
    await authFor(A0, { op: 'add_device', target: sol.solTargetOf({ scheme: 'k256', x: k1.pk.x, y: k1.pk.y, envelope: Number(k1.envelope) } as any) })))).after;
  const ep = ledgerOf(A1).device_epoch as bigint;
  const le = (v: bigint, n: number) => { const o = new Uint8Array(n); let x = v; for (let i = 0; i < n; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
  const w117 = (t: any, e: bigint, c: bigint) => new Uint8Array(createHash('sha256').update(new Uint8Array([...padTag(DESCRIPTOR_TAGS.device.p256), ...A1.addressBytes, ...t.a, ...t.b, ...t.c, ...t.origin, ...le(e, 4), ...le(c, 8)])).digest());
  if (!Buffer.from(w117(tR, ep, 0n)).equals(Buffer.from(pass.device.entryAt(A1.addressBytes, ep, 0n)))) throw new Error('setup: the w117 recipe does not reproduce the passkey entry');
  const plantZ = w117(tZ, ep, 0n);
  const plantR = pass.device.entryAt(A1.addressBytes, ep, 0n);
  let A2 = A1;
  for (const e of [plantZ, plantR]) {
    const l = ledgerOf(A2);
    const kc = (() => { for (let c = 0n; c < 64n; c++) if (l.devices.member(k1.entryAt(A2.addressBytes, l.device_epoch, c))) return c; throw new Error('K not live'); })();
    A2 = (await execute(Original.Contract, A2, 'add_device_with_k256', [e, ...authArgs(k1.sign(k256Challenges.addDevice(ctxOf(A2), k1.pk, e), kc))])).after;
  }
  if (!ledgerOf(A2).devices.member(plantZ) || !ledgerOf(A2).devices.member(plantR)) throw new Error('setup: the plants did not land');
  stateOnly('rules', 'setup: the zero-hash passkey entry (w117 recipe, reproduced for the real hash) and the real one planted by the k256 device', true);
  const remArgs = (t: any, x: any) => [false, msg.solTargetArg(t), msg.solTargetPointArg(t), 0n, ep, Z32, ...authArgs(x)];
  const ctlRem = { a: A2, args: remArgs(tR, await authFor(A2, { op: 'remove_device', literal: false, target: tR, counter: 0n, epoch: ep })) };
  await negative('rules', 'Q46: remove_device by descriptor of a passkey target whose RP hash is zero (its entry live), under a valid signature over the contract\'s bytes', A2, REMOVE,
    remArgs(tZ, await circuitAuth(A2, { op: 'remove_device', literal: false, target: tZ, counter: 0n, epoch: ep })), ZERO_PK, [ZERO_PK], ctlRem);
  // issue_grant
  const COL = fill(32, 0xc1);
  const gP = sol.solGranteeOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y } as any, { origin: pass.policy.origin }, 0n);
  const sP = scopeOf({ read: true, readPk: rnd(), rpIdHash: pass.policy.rp_id_hash });
  const salt = rnd();
  const ctlIssue = { a: A0, args: issueArgsOf(gP, sP, salt, await authFor(A0, { op: 'issue_grant', grantee: gP, ...sP })) };
  const sZ = { ...sP, rpIdHash: new Uint8Array(32) };
  await negative('rules', 'Q46: issue_grant to a passkey grantee whose RP hash is zero, under a valid signature over the contract\'s bytes', A0, ISSUE,
    issueArgsOf(gP, sZ, salt, await circuitAuth(A0, { op: 'issue_grant', grantee: gP, ...sZ })), ZERO_GRANTEE, [ZERO_GRANTEE], ctlIssue);
  const G = await sol.SolEd25519Grantee.enrol(sol.solSoftwareSigner(rnd()), { network: 'undeployed', issuingAccount: A0.addressBytes }, 'Example dApp');
  const sAny = scopeOf({ opWithdrawUnshielded: true, color: COL, maxCoinValue: 100n, perCallCap: 100n, cap: 100n, recipientKind: 0n, recipient: rnd() });
  await negative('rules', 'Q47: issue_grant to any recipient (kind 0) carrying a recipient, under a valid signature over the contract\'s bytes', A0, ISSUE,
    issueArgsOf(G.grantee(0n), sAny, salt, await circuitAuth(A0, { op: 'issue_grant', grantee: G.grantee(0n), ...sAny })), RECIPIENT, [RECIPIENT], ctlIssue);
  await positive('rules', 'Q47: issue_grant to any recipient (kind 0) with a zero recipient: proved (original module)', undefined, A0, ISSUE,
    issueArgsOf(G.grantee(0n), { ...sAny, recipient: Z32 }, salt, await authFor(A0, { op: 'issue_grant', grantee: G.grantee(0n), ...sAny, recipient: Z32 })),
    (after) => ledgerOf(after).grants.member(G.grantId(after.addressBytes, 0n)));
}

// ═════════════════════════════════════════════════════════════════════════════
// Run
// ═════════════════════════════════════════════════════════════════════════════
const startedAt = new Date().toISOString();
let fatal: string | undefined;
try {
  console.log(`sol_ed25519 prover suite: ${SECTIONS.join(', ')}${DRY ? ' (DRY: the JavaScript layer only)' : ''}; proof server ${CONFIG.proofServer}`);
  if (SECTIONS.includes('activation')) await sectionActivation();
  if (SECTIONS.includes('seam')) await sectionSeam();
  if (['replay', 'frame', 'custody', 'witness'].some((s) => SECTIONS.includes(s))) await sectionCustody();
  if (SECTIONS.includes('devices')) await sectionDevices();
  if (SECTIONS.includes('grants')) await sectionGrants();
  if (SECTIONS.includes('grantee-scope')) await sectionGranteeScope();
  if (SECTIONS.includes('frame-lifecycle')) await sectionFrameLifecycle();
  if (SECTIONS.includes('recovery') || SECTIONS.includes('qa-s3')) await sectionRecovery(SECTIONS.includes('recovery'), SECTIONS.includes('qa-s3'));
  if (SECTIONS.includes('readability')) await sectionReadability();
  if (SECTIONS.includes('rules')) await sectionRules();
} catch (e: any) {
  fatal = String(e?.stack ?? e?.message ?? e).split('\n').slice(0, 14).join('\n');
  errors++;
  console.error('ERROR', e);
}
// the counts by refusing layer
const totals: Record<string, number> = {};
const add = (k: string) => { totals[k] = (totals[k] ?? 0) + 1; };
for (const r of results) {
  if (r.kind === 'positive') add(DRY ? 'positive: executed (DRY)' : 'positive: proved');
  else if (r.kind === 'text') add('message text check');
  else if (r.kind === 'state') add('state check (simulator)');
  else if (r.kind === 'not applicable') add('not applicable (reason recorded)');
  else if (r.proverLevel) add('negative: refused by the generated JavaScript only (prover level unreachable, reason recorded)');
  else if (DRY) add('negative: refused by the generated JavaScript (prover not run: DRY)');
  else add(`negative: refused at the proof server, ${r.refusal?.kind}${r.enforcement ? ` (${r.enforcement})` : ''}${r.prover?.verdict !== 'PASS' ? ` [verdict ${r.prover?.verdict}]` : ''}`);
  if (r.prover?.positiveControl) add("positive control proved through a negative's copy");
}
const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  const file = path.join(process.env.EVIDENCE_DIR, `sol-ed25519-prover${SECTIONS === ALL ? '' : `-${SECTIONS.join('-')}`}${DRY ? '-dry' : ''}.json`);
  fs.writeFileSync(file, JSON.stringify(J({ suite: 'sol-ed25519-prover', sections: SECTIONS, dry: DRY, proofServer: CONFIG.proofServer, startedAt, finishedAt: new Date().toISOString(),
    verdict, failures, errors, fatal, totalsByLayer: totals, requests: proofLog.length, transportRetries, cases: results }), null, 2) + '\n');
  console.log(`evidence → ${file}`);
}
console.log(JSON.stringify(totals, null, 1));
console.log(`\n◆ sol-ed25519-prover [${SECTIONS.join(', ')}]: ${verdict} (${results.length} cases, ${failures} failed, ${errors} errors, ${proofLog.length} proof-server requests)${DRY ? ' — DRY' : ''}`);
process.exit(verdict === 'PASS' ? 0 : 1);
