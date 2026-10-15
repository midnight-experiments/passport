// Constraint-level negatives of the base modules, at the proof server.
//
// For every assert of the readable-descriptor and rendering modules, through
// the base probe contract's impure probe_* circuits (and, for Q43, forged
// magnitudes and exact words: digit texts that would shift a magnitude, and
// shown texts other than the circuit's rendering):
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
// Then, for the ed25519 class (a Solana key by its Curve25519Point, spec
// FR-005), the points the type refuses: small-order and mixed-order points
// and a coordinate outside the field, each refused by the generated
// JavaScript's point type and, with that type check replaced (`overrides`,
// after a positive control proved through the same copy), at the layer that
// refuses it next (FR-019): the proof server's input decoding, or the
// runtime's value encoder. The identity passes the type and is refused by the
// A != O assert above.
//
// The calls are built from the probe's constructor state (no deploy, no node,
// no wallet) and only proved, never submitted. Needs a proof server at
// upstream's endpoint (CONFIG.proofServer, 127.0.0.1:6300); a missing proof
// server is an ERROR, never a pass. Writes
// $EVIDENCE_DIR/constraint-negative-prover.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { ed25519, ED25519_TORSION_SUBGROUP } from '@noble/curves/ed25519.js';
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
// A Solana key's point (RFC 8032 section 7.1, TEST 1) and the identity.
const affine = (p: { x: bigint; y: bigint }) => ({ x: p.x, y: p.y });
const PT = affine(ed25519.Point.fromHex('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a').toAffine());
const O = { x: 0n, y: 1n };
// Q43: the magnitude and the exact words.
const MAX = (1n << 128n) - 1n, E37 = 10n ** 37n;
const text = (s: string, w: number) => new Uint8Array(Buffer.from(s.padEnd(w, ' '), 'ascii'));
const d20 = (s: string) => [...text(s, 20)].map(BigInt);
const Z32 = new Uint8Array(32);

// [circuit, honest arguments, bad arguments, the assert the bad call fails]
const CASES: [string, unknown[], unknown[], string][] = [
  ['probe_entry_w52', [pad('midnight:account:device:evm:v1'), A, B20, B32, 0n, 0n], [pad('midnight:account:device:sol:v1'), A, B20, B32, 0n, 0n], 'descriptor: not a 52-byte device tag'],
  ['probe_entry_w64', [pad('midnight:account:device:v1'), A, B32, B32, 0n, 0n], [pad('midnight:account:device:sol:v1'), A, B32, B32, 0n, 0n], 'descriptor: not a 64-byte device tag'],
  ['probe_entry_w65', [pad('midnight:account:device:k1:v2'), A, B32, B32, 1n, 0n, 0n], [pad('midnight:account:device:ed:v1'), A, B32, B32, 1n, 0n, 0n], 'descriptor: not a 65-byte device tag'],
  ['probe_entry_w117', [pad('midnight:account:device:r1:v2'), A, B32, B32, B32, B21, 0n, 0n], [pad('midnight:account:grant:id:r1:v1'), A, B32, B32, B32, B21, 0n, 0n], 'descriptor: not a 117-byte device tag'],
  ['probe_boot_w52', [pad('midnight:account:boot:evm:v1'), B32, B20, B32], [pad('midnight:account:device:evm:v1'), B32, B20, B32], 'descriptor: not a 52-byte boot tag'],
  ['probe_boot_w64', [pad('midnight:account:boot:v1'), B32, B32, B32], [pad('midnight:account:boot:sol:v1'), B32, B32, B32], 'descriptor: not a 64-byte boot tag'],
  ['probe_boot_w65', [pad('midnight:account:boot:k1:v2'), B32, B32, B32, 0n], [fill(32, 0x5a), B32, B32, B32, 0n], 'descriptor: not a 65-byte boot tag'],
  ['probe_boot_w117', [pad('midnight:account:boot:r1:v2'), B32, B32, B32, B32, B21], [pad('midnight:account:boot:v1'), B32, B32, B32, B32, B21], 'descriptor: not a 117-byte boot tag'],
  ['probe_grant_id_w52', [pad('midnight:account:grant:id:evm:v1'), A, B20, B32, B32, 0n], [pad('midnight:account:grant:id:sol:v1'), A, B20, B32, B32, 0n], 'descriptor: not a 52-byte grant-id tag'],
  ['probe_grant_id_w64', [pad('midnight:account:grant:id:r1:v1'), A, B32, B32, B32, 3n], [pad('midnight:account:grant:id:sol:v1'), A, B32, B32, B32, 3n], 'descriptor: not a 64-byte grant-id tag'],
  ['probe_entry_ed25519', [pad('midnight:account:device:sol:v1'), A, PT, B32, 0n, 0n], [pad('midnight:account:device:v1'), A, PT, B32, 0n, 0n], 'descriptor: not an Ed25519 device tag'],
  ['probe_boot_ed25519', [pad('midnight:account:boot:sol:v1'), B32, PT, B32], [pad('midnight:account:boot:v1'), B32, PT, B32], 'descriptor: not an Ed25519 boot tag'],
  ['probe_grant_id_ed25519', [pad('midnight:account:grant:id:sol:v1'), A, PT, B32, B32, 3n], [pad('midnight:account:grant:id:r1:v1'), A, PT, B32, B32, 3n], 'descriptor: not an Ed25519 grant-id tag'],
  ['probe_entry_ed25519', [pad('midnight:account:device:sol:v1'), A, PT, B32, 0n, 0n], [pad('midnight:account:device:sol:v1'), A, O, B32, 0n, 0n], 'descriptor: the Ed25519 key is the identity'],
  ['probe_boot_ed25519', [pad('midnight:account:boot:sol:v1'), B32, PT, B32], [pad('midnight:account:boot:sol:v1'), B32, O, B32], 'descriptor: the Ed25519 key is the identity'],
  ['probe_grant_id_ed25519', [pad('midnight:account:grant:id:sol:v1'), A, PT, B32, B32, 3n], [pad('midnight:account:grant:id:sol:v1'), A, O, B32, B32, 3n], 'descriptor: the Ed25519 key is the identity'],
  ['probe_grant_id_w65', [pad('midnight:account:grant:id:k1:v1'), A, B32, B32, 0n, B32, 3n], [pad('midnight:account:device:k1:v2'), A, B32, B32, 0n, B32, 3n], 'descriptor: not a 65-byte grant-id tag'],
  ['probe_blind', [pad('midnight:account:blind:sol:v1'), fill(64, 0x44)], [spaced('midnight:account:blind:evm:v1'), fill(64, 0x44)], 'descriptor: not a blind tag'],
  ['probe_uint128_text', [1000000n, digits('1000000')], [1000000n, digits('1000001')], 'display: digits do not match the value'],
  ['probe_uint128_text', [7n, digits('7')], [7n, digits('07')], 'display: leading zero'],
  ['probe_label_text_32', [pad('Midnight Night Market')], [pad('Midnight Night Market ')], 'display: not a zero-padded label'],
  ['probe_visible_text_21', [B21], [new Uint8Array(Buffer.from('https://a example.com'))], 'display: not visible ASCII'],
  ['probe_recipient_kind_text', [3n], [4n], 'display: unknown recipient kind'],
  ['probe_k256_envelope_text', [1n], [2n], 'display: unknown signing envelope'],
  // Q43. The magnitude has no input of its own: the digits it comes from are
  // checked, so a text that would shift it is refused (a leading zero would
  // show 10^37 as "0"; a digit after the padding would show 3 as ~3.04 x 10^1).
  ['probe_uint128_magnitude_text', [E37, digits(E37.toString())], [E37, digits('0' + E37.toString())], 'display: leading zero'],
  ['probe_uint128_magnitude_text', [3n, digits('3')], [3n, digits('3 4')], 'display: not a left-aligned decimal'],
  ['probe_uint128_magnitude_text', [MAX - 1n, digits((MAX - 1n).toString())], [MAX - 1n, digits(MAX.toString())], 'display: digits do not match the value'],
  // A shown text other than the circuit's own rendering (an arm binds it
  // through its signed bytes; the probe through an assert).
  ['probe_check_magnitude', [MAX - 1n, digits((MAX - 1n).toString()), text('~3.40 x 10^38', 13)], [MAX - 1n, digits((MAX - 1n).toString()), text('no limit', 13)], "display: the shown magnitude is not the circuit's"],
  ['probe_check_magnitude', [MAX - 1n, digits((MAX - 1n).toString()), text('~3.40 x 10^38', 13)], [MAX - 1n, digits((MAX - 1n).toString()), text('~3.40 x 10^37', 13)], "display: the shown magnitude is not the circuit's"],
  ['probe_check_expiry', [1n, d20('1'), text('1', 20)], [1n, d20('1'), text('never', 20)], "display: the shown expiry is not the circuit's"],
  ['probe_check_expiry', [0n, d20('0'), text('never', 20)], [0n, d20('0'), text('0', 20)], "display: the shown expiry is not the circuit's"],
  ['probe_check_rp_hash', [B32, text(Buffer.from(B32).toString('hex'), 64)], [B32, text('not applicable', 64)], "display: the shown RP hash is not the circuit's"],
  ['probe_check_rp_hash', [Z32, text('not applicable', 64)], [Z32, text('0'.repeat(64), 64)], "display: the shown RP hash is not the circuit's"],
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
// ── The ed25519 class: points the Curve25519Point type refuses ──────────────

const TYPE_BYPASS = Symbol.for('midnight-passport.constraint-negative.curve25519-type');
(globalThis as any)[TYPE_BYPASS] = { refused: 0 };
const typeFired = () => (globalThis as any)[TYPE_BYPASS].refused as number;
// The copy accepts every point at the type check and counts the points the
// original check refuses, so a negative proves the check was reached.
const typeBypassed = await loadBypassedContract(PROBE_JS, [], {
  overrides: `isValidCurve25519Point(p) {
    if (!__compactRuntimeOriginal.isValidCurve25519Point(p)) globalThis[Symbol.for('midnight-passport.constraint-negative.curve25519-type')].refused++;
    return true;
  },`,
});
const typePositive = await expectSuccess({
  name: 'probe_encode_ed25519: an honest point proved through the type-bypassed copy', proofLog: log, through: typeBypassed,
  attempt: () => prove(typeBypassed.Contract, 'probe_encode_ed25519', [PT]),
});
if (typePositive.verdict === 'FAIL') failures++; else if (typePositive.verdict === 'ERROR') errors++;
console.log(`  ${typePositive.verdict === 'PASS' ? '✓' : '✗'} type-bypassed copy positive control: ${typePositive.verdict} (${typePositive.reason})`);
const T = (h: string) => ed25519.Point.fromBytes(Buffer.from(h, 'hex'), true);
const POINTS: [string, { x: bigint; y: bigint }, 'decoding' | 'runtime'][] = [];
for (const h of ED25519_TORSION_SUBGROUP) {
  const p = T(h);
  if (p.is0()) continue; // the identity: the type admits it (A != O above)
  let order = 1n; for (let q = p; !q.is0(); q = q.add(p)) order++;
  POINTS.push([`small order ${order} (${h.slice(0, 8)}…)`, affine(p.toAffine()), 'decoding']);
}
const T8 = T(ED25519_TORSION_SUBGROUP.find((h) => { const p = T(h); return !p.multiply(4n).is0(); })!);
for (const sk of ['4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb', 'c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7']) {
  const A8 = ed25519.Point.fromBytes(ed25519.getPublicKey(Buffer.from(sk, 'hex'))).add(T8);
  POINTS.push([`mixed order A + T8 (${sk.slice(0, 8)}…)`, affine(A8.toAffine()), 'decoding']);
}
POINTS.push(['coordinate y + p (not below p)', { x: PT.x, y: PT.y + ed25519.Point.Fp.ORDER }, 'runtime']);
const pointResults: { point: string; x: string; y: string; runtime: NegativeResult; bypassed: NegativeResult; typeCheckReached: boolean }[] = [];
for (const [name, pt, layer] of POINTS) {
  const runtime = await expectRefusal({ name: `${name}: the point type (generated JavaScript)`, expectedLayer: 'runtime', proofLog: log, attempt: () => prove(Original.Contract, 'probe_encode_ed25519', [pt]) });
  const before = typeFired();
  const bypassed = await expectRefusal({ name: `${name}: type check bypassed`, expectedLayer: layer, bypassed: typeBypassed, proofLog: log, attempt: () => prove(typeBypassed.Contract, 'probe_encode_ed25519', [pt]) });
  const reached = typeFired() > before;
  if (bypassed.verdict === 'PASS' && !reached) { bypassed.verdict = 'FAIL'; bypassed.reason = 'the type-check bypass never saw the point: the tampering missed'; }
  if (runtime.verdict === 'PASS' && !/Curve25519Point/.test(runtime.detail ?? '')) { runtime.verdict = 'FAIL'; runtime.reason = 'refused at runtime, but not by the point type'; }
  if (layer === 'runtime' && bypassed.verdict === 'PASS' && !/expected Curve25519Base/.test(bypassed.detail ?? '')) { bypassed.verdict = 'FAIL'; bypassed.reason = 'refused at runtime, but not by the value encoder'; }
  for (const r of [runtime, bypassed]) { if (r.verdict === 'FAIL') failures++; if (r.verdict === 'ERROR') errors++; }
  pointResults.push({ point: name, x: pt.x.toString(16), y: pt.y.toString(16), runtime, bypassed, typeCheckReached: reached });
  const rej = bypassed.rejection ? `, ${bypassed.rejection.endpoint} ${bypassed.rejection.status} ${bypassed.rejection.rule}` : '';
  console.log(`  ${runtime.verdict === 'PASS' && bypassed.verdict === 'PASS' ? '✓' : '✗'} ${name}: runtime ${runtime.verdict}; type check bypassed: ${bypassed.verdict} (${bypassed.layer}${rej})`);
  if (bypassed.verdict !== 'PASS') console.log(`      ${bypassed.reason} ${bypassed.detail ?? ''}`);
}

const verdict = errors ? 'ERROR' : failures ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'constraint-negative-prover.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify({
    suite: 'constraint-negative-prover', ranAt: new Date().toISOString(), proofServer: CONFIG.proofServer,
    contractAddress, cases: results,
    points: { positiveControl: { ...typePositive, result: undefined }, cases: pointResults,
      note: 'Constraint layer (source-verified, not exercisable through an honest proof server): midnight-zkir 3.1.0-rc.1 assigns a Curve25519Point input with ForeignEdwardsEccChip::assign (midnight-circuits 7.2.4 src/ecc/foreign/edwards_chip.rs: witnesses an h-root Q on the curve and returns [8]Q), so a prover that skips decoding still holds a prime-order point; a small-order input becomes the identity, which A != O refuses.' },
    requests: log.length, verdict,
  }, (_k, v) => (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ constraint-negative-prover: ${verdict} (${CASES.length} asserts, ${POINTS.length} points; ${failures} FAIL, ${errors} ERROR; ${log.length} proof-server requests)`);
process.exit(verdict === 'PASS' ? 0 : 1);
