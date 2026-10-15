// The `evm_eip712` frozen vectors: deterministic inputs for every operation
// and role, and the two adapters that turn one input into (a) a call of the
// contract's pure struct-hash circuit and (b) the typed data a wallet signs.
//
// The frozen file src/tests/vectors/evm-eip712-v2.json holds these inputs
// with the struct hashes, domain separators and digests ethers computed for
// them (Q24). evm-eip712-offline.ts checks the contract and the client codec
// against it; evm-eip712-ethers.ts recomputes it with ethers.

import { createHash } from 'node:crypto';
import {
  evmEip712Messages, toHex, fieldLE,
  type Eip712TypedData, type EvmEip712DescriptorInput, type EvmEip712GranteeInput, type IssueScope,
} from '../wallet/evm-eip712-codec.js';
import { padTag } from '../wallet/descriptors.js';

export const VECTOR_SEED = 'aa00067/e/s4/evm-eip712-vectors/v2';

/** One vector's inputs, JSON-safe: hex strings for bytes, decimal strings for integers. */
export interface VectorInput {
  name: string;
  op: string;
  frame: Record<string, string>;
  args: Record<string, unknown>;
}

const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
/** A 32-byte zero-padded label, raw (no validation: negatives use it too). */
const label = (text: string) => { const o = new Uint8Array(32); o.set(new TextEncoder().encode(text)); return o; };
const unhex = (s: string) => new Uint8Array(Buffer.from(String(s).replace(/^0x/, ''), 'hex'));
const U128 = (1n << 128n) - 1n;
const U64 = (1n << 64n) - 1n;
const U32 = (1n << 32n) - 1n;

export function vectorInputs(): VectorInput[] {
  let ctr = 0;
  const rnd = (n: number) => {
    const out = new Uint8Array(n);
    for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(VECTOR_SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
    return out;
  };
  const r = (n: number) => hex(rnd(n));
  const lead0 = (n: number, zeros: number) => { const b = rnd(n); b.fill(0, 0, zeros); return hex(b); };
  const v: VectorInput[] = [];
  const frames = [
    { account: r(32), device: r(20), authNonce: '0' },
    { account: r(32), device: r(20), authNonce: U64.toString() },
    { account: '00'.repeat(31) + '01', device: '00'.repeat(19) + '01', authNonce: '7' },
  ];
  const gframes = [
    { account: r(32), grantee: r(20), label: hex(label('Midnight Night Market')), slot: '0', issuedAt: '3', grantNonce: '0' },
    { account: r(32), grantee: r(20), label: hex(label('A'.repeat(32))), slot: '255', issuedAt: U64.toString(), grantNonce: U64.toString() },
  ];
  const coin = (value: bigint, idx: bigint) => ({ nonce: r(32), value: value.toString(), mtIndex: idx.toString() });

  frames.forEach((frame, i) => {
    v.push({ name: `withdraw_unshielded#${i}`, op: 'withdrawUnshielded', frame, args: { color: r(32), amount: [1n, U128, 0n][i].toString(), recipient: r(32) } });
    v.push({ name: `withdraw_shielded#${i}`, op: 'withdrawShielded', frame, args: { color: r(32), amount: [5n, U128, 0n][i].toString(), recipient: r(32), coin: coin([7n, U128, 0n][i], [0n, U64, 1n][i]) } });
    v.push({ name: `withdraw_shielded_to_contract#${i}`, op: 'withdrawShieldedToContract', frame, args: { color: r(32), amount: [2n, 1n, 0n][i].toString(), recipientContract: r(32), coin: coin([2n, U128, 9n][i], [3n, 0n, U64][i]) } });
    v.push({ name: `append_inbox#${i}`, op: 'appendInbox', frame, args: { entry: [r(192), lead0(192, 17), '00'.repeat(192)][i] } });
    v.push({ name: `rotate_enc_key#${i}`, op: 'rotateEncKey', frame, args: { newKey: [r(32), lead0(32, 5), 'ff'.repeat(32)][i] } });
    v.push({ name: `remove_unknown_device#${i}`, op: 'removeUnknownDevice', frame, args: { entry: r(32) } });
    v.push({ name: `revoke_all_grants#${i}`, op: 'revokeAllGrants', frame, args: {} });
    v.push({ name: `cancel_recovery#${i}`, op: 'cancelRecovery', frame, args: {} });
    v.push({ name: `publish_recovery_session#${i}`, op: 'publishRecoverySession', frame, args: {
      recoveryPk: { x: BigInt('0x' + r(31)).toString(), y: BigInt('0x' + r(31)).toString() }, sessionNonce: r(32),
      phi: [BigInt('0x' + r(31)), i === 0 ? 0n : BigInt('0x' + r(31)), 0n, i === 1 ? 1n : 0n].map(String),
      phiLen: ['1', '4', '2'][i], wrap: [r(64), lead0(64, 33), '00'.repeat(64)][i] } });
  });

  // Descriptors: one per target scheme, plus edge cases.
  const devices: Record<string, unknown>[] = [
    { scheme: 'evm_eip712', tag: hex(padTag('midnight:account:device:evm:v2')), key: '00'.repeat(32), key2: r(32), address: r(20), envelope: '0', rp_id_hash: '00'.repeat(32), origin: '00'.repeat(21) },
    { scheme: 'sol_ed25519', tag: hex(padTag('midnight:account:device:sol:v1')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '0', rp_id_hash: '00'.repeat(32), origin: '00'.repeat(21) },
    { scheme: 'jubjub', tag: hex(padTag('midnight:account:device:v1')), key: lead0(32, 1), key2: r(32), address: '00'.repeat(20), envelope: '0', rp_id_hash: '00'.repeat(32), origin: '00'.repeat(21) },
    { scheme: 'k256', tag: hex(padTag('midnight:account:device:k1:v2')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '1', rp_id_hash: '00'.repeat(32), origin: '00'.repeat(21) },
    { scheme: 'p256', tag: hex(padTag('midnight:account:device:r1:v2')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '0', rp_id_hash: r(32), origin: hex(new TextEncoder().encode('https://a.example.com')) },
  ];
  devices.forEach((d, i) => {
    v.push({ name: `add_device/${d.scheme}`, op: 'addDevice', frame: frames[i % 3], args: { descriptor: d } });
    v.push({ name: `remove_device/${d.scheme}`, op: 'removeDevice', frame: frames[(i + 1) % 3], args: { descriptor: d, targetEpoch: [0n, 1n, U32, 2n, 0n][i].toString(), targetCounter: [0n, 9n, 1n, U64, 3n][i].toString() } });
  });
  const grantees: Record<string, unknown>[] = [
    { scheme: 'evm_eip712', tag: hex(padTag('midnight:account:grant:id:evm:v2')), key: '00'.repeat(32), key2: r(32), address: r(20), envelope: '0', origin: '00'.repeat(21), label: hex(label('Midnight Night Market')), origin_hash: '00'.repeat(32), slot: '0' },
    { scheme: 'sol_ed25519', tag: hex(padTag('midnight:account:grant:id:sol:v1')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '0', origin: '00'.repeat(21), label: hex(label('x')), origin_hash: '00'.repeat(32), slot: '255' },
    { scheme: 'jubjub', tag: hex(padTag('midnight:account:grant:id:v1')), key: r(32), key2: lead0(32, 2), address: '00'.repeat(20), envelope: '0', origin: '00'.repeat(21), label: '00'.repeat(32), origin_hash: r(32), slot: '1' },
    { scheme: 'k256', tag: hex(padTag('midnight:account:grant:id:k1:v1')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '0', origin: '00'.repeat(21), label: '00'.repeat(32), origin_hash: r(32), slot: '2' },
    { scheme: 'p256', tag: hex(padTag('midnight:account:grant:id:r1:v1')), key: r(32), key2: r(32), address: '00'.repeat(20), envelope: '0', origin: hex(new TextEncoder().encode('https://a.example.com')), label: '00'.repeat(32), origin_hash: '00'.repeat(32), slot: '3' },
  ];
  const scopes = [
    { opWithdrawUnshielded: true, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: false, color: r(32), recipientKind: '1', recipient: r(32),
      maxCoinValue: '100', perCallCap: '10', cap: '100', expiresAt: '0', rpIdHash: '00'.repeat(32), readPk: r(32), windowLen: '0', windowCap: '0', caller: null },
    { opWithdrawUnshielded: true, opWithdrawShielded: true, opWithdrawShieldedToContract: true, read: true, color: r(32), recipientKind: '3', recipient: r(32),
      maxCoinValue: U128.toString(), perCallCap: U128.toString(), cap: U128.toString(), expiresAt: U64.toString(), rpIdHash: r(32), readPk: r(32), windowLen: '0', windowCap: '0', caller: r(32) },
    { opWithdrawUnshielded: false, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: true, color: '00'.repeat(32), recipientKind: '0', recipient: '00'.repeat(32),
      maxCoinValue: '0', perCallCap: '0', cap: '0', expiresAt: '1893456000', rpIdHash: '00'.repeat(32), readPk: lead0(32, 3), windowLen: '0', windowCap: '0', caller: null },
  ];
  grantees.forEach((g, i) => {
    v.push({ name: `issue_grant/${g.scheme}`, op: 'issueGrant', frame: frames[i % 3], args: { grantee: g, scope: scopes[i % 3] } });
    v.push({ name: `revoke_grant/${g.scheme}`, op: 'revokeGrant', frame: frames[(i + 2) % 3], args: { grantee: g } });
  });

  gframes.forEach((frame, i) => {
    v.push({ name: `withdraw_unshielded_as_grantee#${i}`, op: 'withdrawUnshieldedAsGrantee', frame, args: { color: r(32), amount: [9n, U128][i].toString(), recipient: r(32) } });
    v.push({ name: `withdraw_shielded_as_grantee#${i}`, op: 'withdrawShieldedAsGrantee', frame, args: { color: r(32), amount: [3n, U128][i].toString(), recipient: r(32), changeEntry: [lead0(192, 40), r(192)][i], encPk: r(32), coin: coin([10n, U128][i], [5n, U64][i]) } });
    v.push({ name: `withdraw_shielded_to_contract_as_grantee#${i}`, op: 'withdrawShieldedToContractAsGrantee', frame, args: { color: r(32), amount: [3n, 0n][i].toString(), recipientContract: r(32), changeEntry: r(192), encPk: r(32), coin: coin([4n, 0n][i], [0n, 2n][i]) } });
  });
  return v;
}

// ── Adapters ─────────────────────────────────────────────────────────────────

const big = (s: unknown) => BigInt(s as string);
export const descriptorInput = (d: any): EvmEip712DescriptorInput => ({
  tag: unhex(d.tag), key: unhex(d.key), key2: unhex(d.key2), address: unhex(d.address), envelope: big(d.envelope), rp_id_hash: unhex(d.rp_id_hash), origin: unhex(d.origin),
});
export const granteeInput = (g: any): EvmEip712GranteeInput => ({
  tag: unhex(g.tag), key: unhex(g.key), key2: unhex(g.key2), address: unhex(g.address), envelope: big(g.envelope),
  origin: unhex(g.origin), label: unhex(g.label), origin_hash: unhex(g.origin_hash), slot: big(g.slot),
});
const scopeInput = (s: any): IssueScope => ({
  opWithdrawUnshielded: s.opWithdrawUnshielded, opWithdrawShielded: s.opWithdrawShielded, opWithdrawShieldedToContract: s.opWithdrawShieldedToContract,
  read: s.read, color: unhex(s.color), recipientKind: big(s.recipientKind), recipient: unhex(s.recipient), maxCoinValue: big(s.maxCoinValue),
  perCallCap: big(s.perCallCap), cap: big(s.cap), expiresAt: big(s.expiresAt), rpIdHash: unhex(s.rpIdHash), readPk: unhex(s.readPk),
  windowLen: big(s.windowLen), windowCap: big(s.windowCap), caller: s.caller ? unhex(s.caller) : null,
});
const coinInput = (c: any) => ({ nonce: unhex(c.nonce), value: big(c.value), mtIndex: big(c.mtIndex) });
const dframe = (f: any) => ({ account: unhex(f.account), device: unhex(f.device), authNonce: big(f.authNonce) });
const gframeIn = (f: any) => ({ account: unhex(f.account), grantee: unhex(f.grantee), label: unhex(f.label), slot: big(f.slot), issuedAt: big(f.issuedAt), grantNonce: big(f.grantNonce) });

/** The typed data a wallet signs for a vector (the client codec's builders). */
export function typedDataOf(v: VectorInput): Eip712TypedData {
  const a: any = v.args;
  const m = evmEip712Messages as any;
  switch (v.op) {
    case 'withdrawUnshielded': return m.withdrawUnshielded(dframe(v.frame), unhex(a.color), big(a.amount), unhex(a.recipient));
    case 'withdrawShielded': return m.withdrawShielded(dframe(v.frame), unhex(a.color), big(a.amount), unhex(a.recipient), coinInput(a.coin));
    case 'withdrawShieldedToContract': return m.withdrawShieldedToContract(dframe(v.frame), unhex(a.color), big(a.amount), unhex(a.recipientContract), coinInput(a.coin));
    case 'appendInbox': return m.appendInbox(dframe(v.frame), unhex(a.entry));
    case 'rotateEncKey': return m.rotateEncKey(dframe(v.frame), unhex(a.newKey));
    case 'addDevice': return m.addDevice(dframe(v.frame), descriptorInput(a.descriptor));
    case 'removeDevice': return m.removeDevice(dframe(v.frame), descriptorInput(a.descriptor), big(a.targetEpoch), big(a.targetCounter));
    case 'removeUnknownDevice': return m.removeUnknownDevice(dframe(v.frame), unhex(a.entry));
    case 'issueGrant': return m.issueGrant(dframe(v.frame), granteeInput(a.grantee), scopeInput(a.scope));
    case 'revokeGrant': return m.revokeGrant(dframe(v.frame), granteeInput(a.grantee));
    case 'revokeAllGrants': return m.revokeAllGrants(dframe(v.frame));
    case 'publishRecoverySession': return m.publishRecoverySession(dframe(v.frame), {
      recoveryPk: { x: big(a.recoveryPk.x), y: big(a.recoveryPk.y) }, sessionNonce: unhex(a.sessionNonce),
      phi: a.phi.map(big), phiLen: big(a.phiLen), wrap: unhex(a.wrap) });
    case 'cancelRecovery': return m.cancelRecovery(dframe(v.frame));
    case 'withdrawUnshieldedAsGrantee': return m.withdrawUnshieldedAsGrantee(gframeIn(v.frame), unhex(a.color), big(a.amount), unhex(a.recipient));
    case 'withdrawShieldedAsGrantee': return m.withdrawShieldedAsGrantee(gframeIn(v.frame), unhex(a.color), big(a.amount), unhex(a.recipient), unhex(a.changeEntry), unhex(a.encPk), coinInput(a.coin));
    case 'withdrawShieldedToContractAsGrantee': return m.withdrawShieldedToContractAsGrantee(gframeIn(v.frame), unhex(a.color), big(a.amount), unhex(a.recipientContract), unhex(a.changeEntry), unhex(a.encPk), coinInput(a.coin));
  }
  throw new Error(`vector: unknown op ${v.op}`);
}

/** The contract's struct hash for a vector (its exported pure circuits). */
export function contractStructHash(pc: any, v: VectorInput): Uint8Array {
  const a: any = v.args;
  const f: any = v.frame;
  const isGrantee = v.op.endsWith('AsGrantee');
  const dev = isGrantee ? [] : [unhex(f.account), unhex(f.device), big(f.authNonce)];
  const gr = () => [unhex(f.account), unhex(f.grantee), unhex(f.label), big(f.slot), big(f.issuedAt), big(f.grantNonce)];
  const c = a.coin ? [unhex(a.coin.nonce), big(a.coin.value), big(a.coin.mtIndex)] : [];
  switch (v.op) {
    case 'withdrawUnshielded': return pc.evm_eip712_struct_withdraw_unshielded(...dev, unhex(a.color), big(a.amount), unhex(a.recipient));
    case 'withdrawShielded': return pc.evm_eip712_struct_withdraw_shielded(...dev, unhex(a.color), big(a.amount), unhex(a.recipient), ...c);
    case 'withdrawShieldedToContract': return pc.evm_eip712_struct_withdraw_shielded_to_contract(...dev, unhex(a.color), big(a.amount), unhex(a.recipientContract), ...c);
    case 'appendInbox': return pc.evm_eip712_struct_append_inbox(...dev, unhex(a.entry));
    case 'rotateEncKey': return pc.evm_eip712_struct_rotate_enc_key(...dev, unhex(a.newKey));
    case 'addDevice': return pc.evm_eip712_struct_add_device(...dev, descriptorInput(a.descriptor));
    case 'removeDevice': return pc.evm_eip712_struct_remove_device(...dev, descriptorInput(a.descriptor), big(a.targetEpoch), big(a.targetCounter));
    case 'removeUnknownDevice': return pc.evm_eip712_struct_remove_unknown_device(...dev, unhex(a.entry));
    case 'issueGrant': {
      const s = scopeInput(a.scope);
      return pc.evm_eip712_struct_issue_grant(...dev, granteeInput(a.grantee), s.opWithdrawUnshielded, s.opWithdrawShielded, s.opWithdrawShieldedToContract,
        s.read, s.color, s.recipientKind, s.recipient, s.maxCoinValue, s.perCallCap, s.cap, s.expiresAt, s.rpIdHash, s.readPk, s.windowLen, s.windowCap,
        s.caller ? { is_some: true, value: { bytes: s.caller } } : { is_some: false, value: { bytes: new Uint8Array(32) } });
    }
    case 'revokeGrant': return pc.evm_eip712_struct_revoke_grant(...dev, granteeInput(a.grantee));
    case 'revokeAllGrants': return pc.evm_eip712_struct_revoke_all_grants(...dev);
    case 'publishRecoverySession': return pc.evm_eip712_struct_publish_recovery_session(...dev, { x: big(a.recoveryPk.x), y: big(a.recoveryPk.y) },
      unhex(a.sessionNonce), ...a.phi.map(big), big(a.phiLen), unhex(a.wrap));
    case 'cancelRecovery': return pc.evm_eip712_struct_cancel_recovery(...dev);
    case 'withdrawUnshieldedAsGrantee': return pc.evm_eip712_struct_withdraw_unshielded_as_grantee(...gr(), unhex(a.color), big(a.amount), unhex(a.recipient));
    case 'withdrawShieldedAsGrantee': return pc.evm_eip712_struct_withdraw_shielded_as_grantee(...gr(), unhex(a.color), big(a.amount), unhex(a.recipient), unhex(a.changeEntry), unhex(a.encPk), ...c);
    case 'withdrawShieldedToContractAsGrantee': return pc.evm_eip712_struct_withdraw_shielded_to_contract_as_grantee(...gr(), unhex(a.color), big(a.amount), unhex(a.recipientContract), unhex(a.changeEntry), unhex(a.encPk), ...c);
  }
  throw new Error(`vector: unknown op ${v.op}`);
}

/** Negative vectors: inputs every layer named must refuse. */
export interface NegativeVector { name: string; base: string; patch: (v: VectorInput) => VectorInput; refusedBy: ('client' | 'runtime')[]; why: string }
const clone = (v: VectorInput): VectorInput => JSON.parse(JSON.stringify(v));
export const NEGATIVES: NegativeVector[] = [
  { name: 'unregistered device tag', base: 'add_device/k256', refusedBy: ['client', 'runtime'], why: 'tag midnight:account:device:ed:v1 is no registered device tag',
    patch: (v) => { const c = clone(v); (c.args as any).descriptor.tag = hex(padTag('midnight:account:device:ed:v1')); return c; } },
  { name: 'space-padded device tag', base: 'add_device/evm_eip712', refusedBy: ['client', 'runtime'], why: 'a registered text with non-zero padding',
    patch: (v) => { const c = clone(v); const t = padTag('midnight:account:device:evm:v2'); t.fill(32, 'midnight:account:device:evm:v2'.length); (c.args as any).descriptor.tag = hex(t); return c; } },
  { name: 'grant-id tag as a device tag', base: 'remove_device/sol_ed25519', refusedBy: ['client', 'runtime'], why: 'a tag of another recipe',
    patch: (v) => { const c = clone(v); (c.args as any).descriptor.tag = hex(padTag('midnight:account:grant:id:sol:v1')); return c; } },
  { name: 'passkey origin with a space', base: 'add_device/p256', refusedBy: ['client', 'runtime'], why: 'the origin is not visible ASCII',
    patch: (v) => { const c = clone(v); (c.args as any).descriptor.origin = hex(new TextEncoder().encode('https://a example.com')); return c; } },
  { name: 'passkey grantee origin with a NUL', base: 'issue_grant/p256', refusedBy: ['client', 'runtime'], why: 'the origin is not visible ASCII',
    patch: (v) => { const c = clone(v); const o = new TextEncoder().encode('https://a.example.com'); o[20] = 0; (c.args as any).grantee.origin = hex(o); return c; } },
  { name: 'site label ending in a space', base: 'issue_grant/evm_eip712', refusedBy: ['client', 'runtime'], why: 'a label whose text ends in a space is not one-to-one',
    patch: (v) => { const c = clone(v); (c.args as any).grantee.label = hex(label('Midnight ')); return c; } },
  { name: 'site label with a double space', base: 'revoke_grant/sol_ed25519', refusedBy: ['client', 'runtime'], why: 'words are separated by single spaces',
    patch: (v) => { const c = clone(v); (c.args as any).grantee.label = hex(label('a  b')); return c; } },
  { name: 'empty site label', base: 'withdraw_unshielded_as_grantee#0', refusedBy: ['client', 'runtime'], why: 'an all-zero label shows nothing',
    patch: (v) => { const c = clone(v); (c.frame as any).label = '00'.repeat(32); return c; } },
  { name: 'unregistered grant-id tag', base: 'revoke_grant/k256', refusedBy: ['client', 'runtime'], why: 'a device tag is no grant-id tag',
    patch: (v) => { const c = clone(v); (c.args as any).grantee.tag = hex(padTag('midnight:account:device:k1:v2')); return c; } },
  { name: 'amount above the spent coin', base: 'withdraw_shielded#0', refusedBy: ['client', 'runtime'], why: 'change would be negative',
    patch: (v) => { const c = clone(v); (c.args as any).amount = '8'; return c; } },
  { name: 'grantee amount above the spent coin', base: 'withdraw_shielded_as_grantee#0', refusedBy: ['client', 'runtime'], why: 'change would be negative',
    patch: (v) => { const c = clone(v); (c.args as any).amount = '11'; return c; } },
  { name: 'amount of 2^128', base: 'withdraw_unshielded#0', refusedBy: ['client', 'runtime'], why: 'uint128 out of range',
    patch: (v) => { const c = clone(v); (c.args as any).amount = (1n << 128n).toString(); return c; } },
  { name: 'auth nonce of 2^64', base: 'rotate_enc_key#0', refusedBy: ['client', 'runtime'], why: 'uint64 out of range',
    patch: (v) => { const c = clone(v); (c.frame as any).authNonce = (1n << 64n).toString(); return c; } },
  { name: '191-byte inbox entry', base: 'append_inbox#0', refusedBy: ['client', 'runtime'], why: 'the ciphertext is exactly 192 bytes',
    patch: (v) => { const c = clone(v); (c.args as any).entry = (c.args as any).entry.slice(2); return c; } },
];

export { hex as vectorHex, unhex as vectorUnhex, fieldLE as vectorFieldLE, toHex as vectorToHex };
