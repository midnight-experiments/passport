// Arm `sol_ed25519`: the signed messages (format sol v1), offline.
//
// The contract's `sol_message_<operation>` pure circuits against the
// independent TypeScript renderer (src/wallet/sol-ed25519-message.ts), byte
// for byte, over a corpus covering all 15 layouts, both roles, every target
// class, and edge values (0, 1, 2^64 - 1, 2^128 - 1, 18 decimals, 8-character
// symbols, 32-byte labels). Also: every layout has one fixed length below
// the Solana parse bound; every line starts with circuit-fixed text; a site
// label changes only the Site line; display inputs that do not describe the
// value are refused by the circuit (runtime) and by the renderer (client).
// The corpus is frozen in src/tests/vectors/sol-ed25519-messages-v1.json:
// a run compares against it, or writes it when SOL_MESSAGES_WRITE=1.
//
// Writes $EVIDENCE_DIR/sol-ed25519-message-offline.json when set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { pureCircuits } from '../wallet/contract.js';
import { solDeviceMessageCircuit, solGranteeMessageCircuit } from '../wallet/signer-sol-ed25519.js';
import {
  SOL_PARSE_BOUND, assertSafeSolMessage, digitsOf, labelBytes, nibblesOf, solAmountShow, solCoinShow, solDeviceMessageText,
  solGranteeArg, solGranteeMessageText, solGranteeShow, solGrantShow, solMessageBytes, solScopeShow, solShow,
  solTargetArg, solTargetShow, type SolAmount, type SolCoin, type SolDeviceContext, type SolDeviceOperation,
  type SolGranteeContext, type SolGranteeFields, type SolGranteeOperation, type SolTargetFields,
} from '../wallet/sol-ed25519-message.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FROZEN = path.join(HERE, 'vectors', 'sol-ed25519-messages-v1.json');
const pc: any = pureCircuits;

interface Case { group: string; name: string; verdict: 'PASS' | 'FAIL'; layer?: string; detail?: string }
const cases: Case[] = [];
const ok = (group: string, name: string, cond: boolean, detail?: string, layer?: string) => {
  cases.push({ group, name, verdict: cond ? 'PASS' : 'FAIL', ...(layer ? { layer } : {}), ...(detail ? { detail } : {}) });
  if (!cond) console.log(`  ✗ ${group}: ${name}${detail ? ` — ${detail}` : ''}`);
};
const refused = (group: string, name: string, layer: string, re: RegExp, fn: () => unknown) => {
  try { fn(); ok(group, name, false, 'accepted (expected a refusal)', layer); } catch (e: any) {
    const m = String(e?.message ?? e); ok(group, name, re.test(m), m.slice(0, 160), layer);
  }
};

// Deterministic test bytes.
const det = (seed: string, n: number) => {
  const out = new Uint8Array(n); let h = createHash('sha256').update(seed).digest(); let i = 0;
  while (i < n) { out.set(h.subarray(0, Math.min(32, n - i)), i); i += 32; h = createHash('sha256').update(h).digest(); }
  return out;
};
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const MAX64 = (1n << 64n) - 1n, MAX128 = (1n << 128n) - 1n;
const le32 = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 0; i < 32; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const FIELD_MAX = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000n;

const SITES = ['Example Wallet', 'a', 'Site: Add a device', 'Consequence: none', 'x'.repeat(32), 'Account 00 nonce 1'];
const AMOUNTS: SolAmount[] = [
  { color: det('c1', 32), amount: 1_000_000n, decimals: 6, symbol: 'tUSDC' },
  { color: new Uint8Array(32), amount: 0n, decimals: 0, symbol: 'NIGHT' },
  { color: det('c3', 32), amount: MAX128, decimals: 18, symbol: 'ABCDEFGH' },
  { color: det('c4', 32), amount: 5n, decimals: 18, symbol: '?' },
];
const coinFor = (a: SolAmount, extra: bigint, idx: bigint): SolCoin => ({ nonce: det(`n${extra}`, 32), color: a.color, value: a.amount + extra > MAX128 ? MAX128 : a.amount + extra, mt_index: idx });

const TARGETS: SolTargetFields[] = [
  { tag: 'midnight:account:device:evm:v2', address: det('evm', 20), a: det('blind-e', 32) },
  { tag: 'midnight:account:device:v1', a: det('jx', 32), b: det('jy', 32) },
  { tag: 'midnight:account:device:sol:v1', a: det('sk', 32), b: det('blind-s', 32) },
  { tag: 'midnight:account:device:k1:v2', a: det('kx', 32), b: det('ky', 32), envelope: 1n },
  { tag: 'midnight:account:device:r1:v2', a: det('rx', 32), b: det('ry', 32), c: det('rp', 32), origin: new TextEncoder().encode('https://a.example.com') },
];
const GRANTEES: SolGranteeFields[] = [
  { tag: 'midnight:account:grant:id:evm:v2', address: det('gevm', 20), a: det('gblind-e', 32), label: 'Example dApp', slot: 0n },
  { tag: 'midnight:account:grant:id:v1', a: det('gjx', 32), b: det('gjy', 32), originHash: det('goh-j', 32), slot: 7n },
  { tag: 'midnight:account:grant:id:sol:v1', a: det('gsk', 32), b: det('gblind-s', 32), label: 'x'.repeat(32), slot: 255n },
  { tag: 'midnight:account:grant:id:k1:v1', a: det('gkx', 32), b: det('gky', 32), envelope: 0n, originHash: det('goh-k', 32), slot: 1n },
  { tag: 'midnight:account:grant:id:r1:v1', a: det('grx', 32), b: det('gry', 32), origin: new TextEncoder().encode('https://b.example.org'), slot: 2n },
];

type Built = { name: string; op: string; text: string; circuit: Uint8Array };
const corpus: Built[] = [];

// The contract side: the facade's calls of the contract's pure circuits.
const deviceCall = (ctx: SolDeviceContext, o: SolDeviceOperation): Uint8Array =>
  solDeviceMessageCircuit(ctx.key, { contractAddress: ctx.account, authNonce: ctx.nonce }, ctx.site, o).bytes;
const granteeCall = (ctx: SolGranteeContext, o: SolGranteeOperation): Uint8Array =>
  solGranteeMessageCircuit(ctx.key, { contractAddress: ctx.account, label: ctx.label, slot: ctx.slot, issuedAt: ctx.issuedAt, grantNonce: ctx.nonce }, ctx.site, o).bytes;

// ── 1. The corpus: circuit == renderer ──────────────────────────────────────
const devCtx = (i: number): SolDeviceContext => ({ site: SITES[i % SITES.length], account: det(`acct${i}`, 32), key: det(`key${i}`, 32), nonce: [0n, 1n, 17n, MAX64][i % 4] });
const grCtx = (i: number): SolGranteeContext => ({ ...devCtx(i), label: ['Example dApp', 'z', 'x'.repeat(32)][i % 3], slot: [0n, 3n, 255n][i % 3], issuedAt: [0n, 5n, MAX64][i % 3] });
const devOps: [string, SolDeviceOperation][] = [];
devOps.push(['rotate_enc_key', { op: 'rotate_enc_key', newKey: det('nk', 32) }]);
devOps.push(['rotate_enc_key zero', { op: 'rotate_enc_key', newKey: new Uint8Array(32) }]);
devOps.push(['append_inbox', { op: 'append_inbox', entry: det('entry', 192) }]);
devOps.push(['append_inbox 0xff', { op: 'append_inbox', entry: new Uint8Array(192).fill(255) }]);
AMOUNTS.forEach((a, i) => {
  devOps.push([`withdraw_unshielded ${i}`, { op: 'withdraw_unshielded', amount: a, recipient: det(`ru${i}`, 32) }]);
  devOps.push([`withdraw_shielded ${i}`, { op: 'withdraw_shielded', amount: a, recipient: det(`rs${i}`, 32), coin: coinFor(a, BigInt(i) * 7n, BigInt(i) * 1000n) }]);
  devOps.push([`withdraw_shielded_to_contract ${i}`, { op: 'withdraw_shielded_to_contract', amount: a, recipient: det(`rc${i}`, 32), coin: coinFor(a, 0n, MAX64) }]);
});
TARGETS.forEach((t) => {
  devOps.push([`add_device ${t.tag}`, { op: 'add_device', target: t }]);
  devOps.push([`remove_device ${t.tag}`, { op: 'remove_device', literal: false, target: t, counter: 4n, epoch: 1n }]);
});
devOps.push(['remove_device max counter/epoch', { op: 'remove_device', literal: false, target: TARGETS[2], counter: MAX64, epoch: 0xffffffffn }]);
devOps.push(['remove_device literal', { op: 'remove_device', literal: true, entry: det('lit', 32) }]);
GRANTEES.forEach((g, i) => {
  const spend = i !== 4;
  devOps.push([`issue_grant ${g.tag}`, { op: 'issue_grant', grantee: g, opWithdrawUnshielded: spend, opWithdrawShielded: i % 2 === 0, opWithdrawShieldedToContract: i === 2,
    read: i % 2 === 0, color: det(`gc${i}`, 32), recipientKind: BigInt(i % 4), recipient: i % 4 === 0 ? new Uint8Array(32) : det(`gr${i}`, 32),
    maxCoinValue: [MAX128, 1000n, 1n, 50n, 0n][i], perCallCap: [MAX128, 100n, 1n, 50n, 0n][i], cap: [MAX128, 1000n, 1n, 100n, 0n][i],
    expiresAt: [0n, 1_800_000_000n, MAX64, 1n, 0n][i], rpIdHash: i === 4 ? det('rph', 32) : new Uint8Array(32), readPk: i % 2 === 0 ? det(`rk${i}`, 32) : new Uint8Array(32),
    windowLen: 0n, windowCap: 0n, caller: i === 1 ? det('caller', 32) : null }]);
  devOps.push([`revoke_grant ${g.tag}`, { op: 'revoke_grant', grantee: g }]);
});
devOps.push(['revoke_all_grants', { op: 'revoke_all_grants' }]);
devOps.push(['publish_recovery_session', { op: 'publish_recovery_session', recoveryPk: pc.compute_public_point_with_jubjub(5n), sessionNonce: det('sn', 32), phi: [1n, FIELD_MAX, 0n, 0n], phiLen: 2n, wrap: det('wrap', 64) }]);
devOps.push(['publish_recovery_session 4', { op: 'publish_recovery_session', recoveryPk: pc.compute_public_point_with_jubjub(FIELD_MAX), sessionNonce: det('sn4', 32), phi: [5n, 6n, 7n, 8n], phiLen: 4n, wrap: new Uint8Array(64) }]);
devOps.push(['recover_cancel', { op: 'recover_cancel' }]);
const grOps: [string, SolGranteeOperation][] = [];
AMOUNTS.forEach((a, i) => {
  grOps.push([`withdraw_unshielded_with_grant ${i}`, { op: 'withdraw_unshielded_with_grant', amount: a, recipient: det(`gru${i}`, 32) }]);
  grOps.push([`withdraw_shielded_with_grant ${i}`, { op: 'withdraw_shielded_with_grant', amount: a, recipient: det(`grs${i}`, 32), changeEntry: det(`ce${i}`, 192), encPk: det(`ek${i}`, 32), coin: coinFor(a, 9n, BigInt(i)) }]);
  grOps.push([`withdraw_shielded_to_contract_with_grant ${i}`, { op: 'withdraw_shielded_to_contract_with_grant', amount: a, recipient: det(`grc${i}`, 32), changeEntry: det(`cc${i}`, 192), encPk: det(`ec${i}`, 32), coin: coinFor(a, 0n, MAX64) }]);
});

{
  const G = '1 circuit == renderer';
  let n = 0;
  devOps.forEach(([name, o], i) => {
    const ctx = devCtx(i);
    const text = solDeviceMessageText(ctx, o);
    const circuit: Uint8Array = deviceCall(ctx, o);
    const same = Buffer.from(circuit).toString('latin1') === text;
    if (same) n++; else ok(G, name, false, `circuit ${circuit.length} B vs renderer ${text.length} B`);
    corpus.push({ name, op: o.op, text, circuit });
  });
  grOps.forEach(([name, o], i) => {
    const ctx = grCtx(i);
    const text = solGranteeMessageText(ctx, o);
    const circuit: Uint8Array = granteeCall(ctx, o);
    const same = Buffer.from(circuit).toString('latin1') === text;
    if (same) n++; else ok(G, name, false, `circuit ${circuit.length} B vs renderer ${text.length} B`);
    corpus.push({ name, op: o.op, text, circuit });
  });
  ok(G, `all ${corpus.length} calls byte-identical (15 layouts, both roles, 5 target classes, 5 grantee classes, edge values)`, n === corpus.length, `${n}/${corpus.length}`);
}

// ── 2. Lengths, parse safety, line starts ───────────────────────────────────
const LINE_STARTS = [
  'Midnight Passport approval (sol v1)', 'Operation: ', 'Site: ', 'Role: ', 'Account: ', 'Signing key: ', 'New encryption key: ', 'Consequence: ',
  'Device nonce: ', 'Inbox entry ', 'Token: ', 'Amount (base units): ', 'This site labels it: ', 'To unshielded address: ', 'To shielded key: ',
  'To contract: ', 'Spent coin value: ', 'Spent coin nonce: ', 'Spent coin index: ', 'Change back to this account: ', 'Device scheme: ',
  'Ethereum address: 0x', 'Device privacy salt: ', 'JubJub key x: ', 'JubJub key y: ', 'Solana key: ', 'secp256k1 key x: ', 'secp256k1 key y: ',
  'Signing envelope: ', 'Passkey key x: ', 'Passkey key y: ', 'Passkey origin: ', 'Passkey RP (hash): ', 'Device use counter: ', 'Device epoch: ',
  'Removes a device this wallet cannot identify', 'Device entry: ', 'Grantee scheme: ', 'Grantee label: ', 'Grantee site label (hash): ',
  'Grantee slot: ', 'May withdraw unshielded: ', 'May withdraw shielded: ', 'May withdraw shielded to a contract: ', 'May read the inbox: ',
  'Recipient kind: ', 'Recipient: ', 'Max coin value: ', 'Per-call cap: ', 'Total cap: ', 'Expires at (block time, seconds; 0 = never): ',
  'Inbox read key: ', 'Window length: ', 'Window cap: ', 'Caller restricted to a contract: ', 'Caller: ', 'Recovery key x: ', 'Recovery key y: ',
  'Session nonce: ', 'Backup vector value ', 'Backup vector length: ', 'Key wrap part ', 'Change entry ', 'Grant label: ', 'Grant slot: ',
  'Grant issued at nonce: ', 'Grant use nonce: ',
];
const lengths: Record<string, number> = {};
{
  const G = '2 lengths, parse bound, line starts';
  let fixed = true, safe = true, starts = true;
  for (const c of corpus) {
    const key = c.op + (c.op.endsWith('_with_grant') ? '' : '');
    if (lengths[key] === undefined) lengths[key] = c.text.length; else if (lengths[key] !== c.text.length) { fixed = false; ok(G, `fixed length ${c.name}`, false, `${c.text.length} vs ${lengths[key]}`); }
    try { assertSafeSolMessage(c.circuit); solMessageBytes(c.text); } catch (e: any) { safe = false; ok(G, `parse-safe ${c.name}`, false, e.message); }
    for (const line of c.text.split('\n')) if (!LINE_STARTS.some((p) => line.startsWith(p))) { starts = false; ok(G, `line start in ${c.name}`, false, JSON.stringify(line.slice(0, 50))); }
  }
  ok(G, `one fixed length per layout (${Object.keys(lengths).length} layouts)`, fixed && Object.keys(lengths).length === 15);
  const max = Math.max(...Object.values(lengths));
  ok(G, `every layout below the parse bound (max ${max} < ${SOL_PARSE_BOUND})`, safe && max < SOL_PARSE_BOUND);
  ok(G, 'every line of every message starts with circuit-fixed text', starts);
  ok(G, 'the parse bound is 3 + 1 + 110*32 + 32 + 1 = 3,557 for a message starting "Midn"', SOL_PARSE_BOUND === 3557 && 'Midn'.charCodeAt(3) === 110);
}

// ── 2b. An independent parse of Solana's wire formats (FR-S03) ──────────────
// Legacy message: header (num_required_signatures, num_readonly_signed,
// num_readonly_unsigned), compact-u16 key count, keys (32 each), recent
// blockhash (32), compact-u16 instruction count, instructions (program index,
// compact-u16 account count, indices, compact-u16 data length, data), nothing
// left over. Transaction: compact-u16 signature count, signatures (64 each),
// then a message (legacy, or versioned when the first byte has bit 7 set).
function cu16(b: Uint8Array, i: number): [number, number] | null {
  let v = 0;
  for (let k = 0; k < 3; k++) {
    if (i + k >= b.length) return null;
    const x = b[i + k];
    v |= (x & 0x7f) << (7 * k);
    if (!(x & 0x80)) return [v, i + k + 1];
  }
  return null;
}
function parseLegacyMessage(b: Uint8Array, start = 0): { ok: boolean; sanitized: boolean; end: number } {
  let i = start;
  if (b.length < i + 3) return { ok: false, sanitized: false, end: i };
  const [req, ros, rou] = [b[i], b[i + 1], b[i + 2]]; i += 3;
  const n = cu16(b, i); if (!n) return { ok: false, sanitized: false, end: i };
  const [keys, j] = n; i = j + keys * 32 + 32;
  if (i > b.length) return { ok: false, sanitized: false, end: i };
  const m = cu16(b, i); if (!m) return { ok: false, sanitized: false, end: i };
  let [ix, k] = m; i = k;
  for (let t = 0; t < ix; t++) {
    i += 1; const a = cu16(b, i); if (!a) return { ok: false, sanitized: false, end: i }; i = a[1] + a[0];
    const d = cu16(b, i); if (!d) return { ok: false, sanitized: false, end: i }; i = d[1] + d[0];
    if (i > b.length) return { ok: false, sanitized: false, end: i };
  }
  const ok = i === b.length;
  // Message::sanitize: a writable fee payer (num_readonly_signed < num_required)
  // and enough keys for the signers and the read-only unsigned ones.
  return { ok, sanitized: ok && ros < req && req + rou <= keys, end: i };
}
function parsesAsTransaction(b: Uint8Array): boolean {
  const n = cu16(b, 0); if (!n) return false;
  const i = n[1] + n[0] * 64; if (i >= b.length) return false;
  return (b[i] & 0x80) ? false : parseLegacyMessage(b, i).ok;
}
{
  const G = '2b Solana wire formats (independent parser)';
  ok(G, 'no corpus message parses as a legacy message, a versioned message or a transaction', corpus.every((c) =>
    !parseLegacyMessage(c.circuit).ok && !(c.circuit[0] & 0x80) && !parsesAsTransaction(c.circuit) && c.circuit[0] !== 0xff));
  const first = corpus[0].circuit.subarray(0, 4);
  const at = (n: number) => { const b = new Uint8Array(n); b.set(first); return b; };
  ok(G, `the bound is tight: a "Midn" buffer of ${SOL_PARSE_BOUND} bytes parses as a legacy message, ${SOL_PARSE_BOUND - 1} bytes does not`,
    parseLegacyMessage(at(SOL_PARSE_BOUND)).ok && !parseLegacyMessage(at(SOL_PARSE_BOUND - 1)).ok);
  ok(G, 'and even then it never sanitizes: header (77, 105, 100) has no writable fee payer (105 >= 77)', !parseLegacyMessage(at(SOL_PARSE_BOUND)).sanitized);
  ok(G, 'as a transaction a "Midn" prefix claims 77 signatures (4,928 bytes before the message)', cu16(first, 0)![0] === 77);
}

// ── 3. The site's label changes only the Site line ──────────────────────────
{
  const G = '3 site label isolation';
  let good = true;
  for (const site of SITES.slice(1)) {
    const a = solDeviceMessageText(devCtx(0), devOps[0][1]);
    const ctx = { ...devCtx(0), site };
    const circuit = Buffer.from(deviceCall(ctx, devOps[0][1])).toString('latin1');
    const la = a.split('\n'), lb = circuit.split('\n');
    const diffs = la.map((l, i) => (l === lb[i] ? -1 : i)).filter((i) => i >= 0);
    if (!(diffs.length === 1 && la[diffs[0]].startsWith('Site: '))) good = false;
  }
  ok(G, 'another label changes the Site line only, and an imitating label stays after "Site: "', good);
}

// ── 4. Display inputs that do not describe the value ────────────────────────
{
  const G = '4 display-input refusals';
  const ctx = devCtx(1), self = { bytes: ctx.account };
  const a = AMOUNTS[0];
  const recipient = det('r', 32);
  const good = solAmountShow(a);
  const goodHex = nibblesOf(ctx.account, ctx.key, a.color, recipient);
  const run = (show: any, amountShow: any, hex: bigint[] = goodHex) =>
    pc.sol_message_withdraw_unshielded(self, ctx.key, ctx.nonce, a.color, a.amount, { bytes: recipient }, amountShow, show, hex);
  const asc = (s: string, w: number) => [...Buffer.from(s.padEnd(w, ' '), 'ascii')].map(BigInt);
  const site = (s: string) => { const o = new Array(32).fill(0n); [...Buffer.from(s, 'latin1')].forEach((c, i) => { if (i < 32) o[i] = BigInt(c); }); return o; };
  const base = solShow(ctx.site, ctx.nonce);
  ok(G, 'positive control: the honest inputs render', run(base, good).length === 620);
  const bad: [string, any, any, bigint[] | undefined, RegExp][] = [
    ['amount digits of another value', base, { ...good, units: asc('1000001', 39) }, undefined, /digits do not match/],
    ['amount with a leading zero', base, { ...good, units: asc('01000000', 39) }, undefined, /leading zero|digits do not match/],
    ['amount right-aligned', base, { ...good, units: asc('', 32).concat(asc('1000000', 7)) }, undefined, /not a left-aligned decimal|empty decimal/],
    ['claim digits of another value', base, { ...good, claim: asc('1.000001 tUSDC', 49) }, undefined, /digits do not match/],
    ['claim with 19 decimals', base, { ...good, claim: asc('0.0000000000001000000 tUSDC', 49) }, undefined, /more than 18 decimals/],
    ['claim symbol of 9 characters', base, { ...good, claim: asc('1.000000 ABCDEFGHI', 49) }, undefined, /symbol longer than 8/],
    ['claim with a line break', base, { ...good, claim: asc('1.000000 tUS\nDC', 49) }, undefined, /not a site amount label/],
    ['nonce digits of another value', { ...base, nonce: asc('2', 20) }, good, undefined, /digits do not match/],
    ['site label with a leading space', { ...base, site: site(' Example') }, good, undefined, /not a zero-padded label/],
    ['site label with two spaces', { ...base, site: site('Example  Wallet') }, good, undefined, /not a zero-padded label/],
    ['site label with a line break', { ...base, site: site('Example\nDevice nonce: 0') }, good, undefined, /not a zero-padded label/],
    ['site label with a byte after the padding', { ...base, site: [...site('Example'), ].map((c, i) => (i === 20 ? 65n : c)) }, good, undefined, /not a zero-padded label/],
    ['empty site label', { ...base, site: new Array(32).fill(0n) }, good, undefined, /not a zero-padded label/],
    ['hex nibbles of another account', base, good, nibblesOf(det('other', 32), ctx.key, a.color, recipient), /hex digits do not match/],
    ['hex nibbles off by one in the recipient', base, good, goodHex.map((n, i) => (i === goodHex.length - 1 ? (n + 1n) % 16n : n)), /hex digits do not match/],
    ['hex nibble 16 (not a nibble)', base, good, goodHex.map((n, i) => (i === 0 ? 16n : n)), /type error|Uint<0..16>|out of range|expected/i],
  ];
  for (const [name, show, amountShow, hex, re] of bad) refused(G, `${name}: circuit`, 'runtime', re, () => run(show, amountShow, hex));
  refused(G, 'site label with a line break: renderer', 'client', /label/, () => labelBytes('Example\nDevice'));
  refused(G, 'site label longer than 32 bytes: renderer', 'client', /at most 32/, () => labelBytes('x'.repeat(33)));
  const ig = devOps.find(([n]) => n.startsWith('issue_grant'))![1] as any;
  refused(G, 'unknown recipient kind: circuit', 'runtime', /unknown recipient kind/, () => deviceCall(devCtx(0), { ...ig, recipientKind: 4n }));
  refused(G, 'unregistered target tag: circuit', 'runtime', /not a registered device tag/, () => {
    const c0 = devCtx(0); const t = { ...TARGETS[2], tag: 'midnight:account:device:ed:v1' };
    return pc.sol_message_add_device({ bytes: c0.account }, c0.key, c0.nonce, { ...solTargetArg(TARGETS[2]), tag: (() => { const o = new Uint8Array(32); o.set(Buffer.from(t.tag)); return o; })() },
      solTargetShow(TARGETS[2]), solShow(c0.site, c0.nonce), nibblesOf(c0.account, c0.key, new Uint8Array(20), TARGETS[2].a!, TARGETS[2].b!, new Uint8Array(32)));
  });
  refused(G, 'passkey origin characters of another origin: circuit', 'runtime', /characters do not match/, () => {
    const c0 = devCtx(0); const t = TARGETS[4];
    return pc.sol_message_add_device({ bytes: c0.account }, c0.key, c0.nonce, solTargetArg(t), { ...solTargetShow(t), origin: [...Buffer.from('https://b.example.com')].map(BigInt) },
      solShow(c0.site, c0.nonce), nibblesOf(c0.account, c0.key, new Uint8Array(20), t.a!, t.b!, t.c!));
  });
  refused(G, 'non-visible passkey origin: circuit', 'runtime', /not visible ASCII/, () => deviceCall(devCtx(0), { op: 'add_device', target: { ...TARGETS[4], origin: new TextEncoder().encode('https://a example.com') } }));
  refused(G, 'grant label characters of another label: circuit', 'runtime', /characters do not match/, () => {
    const c = grCtx(0), o = grOps[0][1] as any;
    return pc.sol_message_withdraw_unshielded_with_grant({ bytes: c.account }, c.key, labelBytes(c.label), c.slot, c.issuedAt, c.nonce, o.amount.color, o.amount.amount,
      { bytes: o.recipient }, solAmountShow(o.amount), solShow(c.site, c.nonce), { ...solGrantShow(c.label, c.slot, c.issuedAt), label: [...labelBytes('Another dApp')].map(BigInt) },
      nibblesOf(c.account, c.key, o.amount.color, o.recipient));
  });
  {
    const c0 = devCtx(0), coin = { ...coinFor(AMOUNTS[0], 0n, 0n), value: 1n };
    const coinShow = { value: digitsOf(1n, 39), index: digitsOf(0n, 20), change: digitsOf(0n, 39) };
    refused(G, 'withdrawal above the spent coin: circuit', 'runtime', /above the spent coin/, () => pc.sol_message_withdraw_shielded(
      { bytes: c0.account }, c0.key, c0.nonce, { bytes: det('x', 32) }, AMOUNTS[0].color, AMOUNTS[0].amount, coin, solAmountShow(AMOUNTS[0]), coinShow,
      solShow(c0.site, c0.nonce), nibblesOf(c0.account, c0.key, AMOUNTS[0].color, det('x', 32), coin.nonce)));
    refused(G, 'withdrawal above the spent coin: renderer', 'client', /above the spent coin/, () => solDeviceMessageText(c0, { op: 'withdraw_shielded', amount: AMOUNTS[0], recipient: det('x', 32), coin }));
  }
}

// ── 5. The frozen corpus ────────────────────────────────────────────────────
{
  const G = '5 frozen corpus';
  // Negative vectors: every refusal of section 4, with its refusing layer.
  const negatives = cases.filter((c) => c.layer).map((c) => ({ name: c.name, layer: c.layer, refusal: (c.detail ?? '').replace(/^.*?(failed assert: |sol message: |type error: )/, '$1').slice(0, 120) }));
  const frozen = { format: 'sol v1', lengths, calls: corpus.map((c) => ({ name: c.name, op: c.op, bytes: c.text.length, sha256: createHash('sha256').update(c.circuit).digest('hex'), text: c.text })), negatives };
  if (process.env.SOL_MESSAGES_WRITE === '1') {
    fs.writeFileSync(FROZEN, JSON.stringify(frozen, null, 2) + '\n');
    ok(G, `wrote ${FROZEN}`, true);
  } else if (!fs.existsSync(FROZEN)) {
    ok(G, 'frozen corpus present', false, `${FROZEN} missing (SOL_MESSAGES_WRITE=1 writes it)`);
  } else {
    const f = JSON.parse(fs.readFileSync(FROZEN, 'utf8'));
    const same = JSON.stringify(f) === JSON.stringify(frozen);
    ok(G, `corpus equals the frozen file (${frozen.calls.length} calls)`, same, same ? undefined : 'differs: the grammar changed, which needs a new format version');
  }
}

const failed = cases.filter((c) => c.verdict !== 'PASS');
for (const g of [...new Set(cases.map((c) => c.group))]) {
  const cs = cases.filter((c) => c.group === g);
  console.log(`  ${cs.every((c) => c.verdict === 'PASS') ? '✓' : '✗'} ${g}: ${cs.filter((c) => c.verdict === 'PASS').length}/${cs.length}`);
}
console.log('  lengths:', JSON.stringify(lengths));
const verdict = failed.length ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(path.join(process.env.EVIDENCE_DIR, 'sol-ed25519-message-offline.json'),
    JSON.stringify({ suite: 'sol-ed25519-message-offline', ranAt: new Date().toISOString(), lengths, cases, verdict }, null, 2) + '\n');
}
console.log(`\n◆ sol-ed25519-message-offline: ${verdict} (${cases.length} cases, ${failed.length} failed; corpus ${corpus.length} calls)`);
process.exit(verdict === 'PASS' ? 0 : 1);
