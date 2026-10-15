// Offline suite of the `evm_eip712` arm (contracts/account-evm-eip712.compact,
// src/wallet/signer-evm-eip712.ts). No node, no proof server.
//
//   recipes      derive_{device_entry,boot_commitment,grant_id}_with_evm_eip712
//                equal the descriptor module's width-52 circuits and SHA-256 of
//                the specified preimage (Node crypto), on seeded vectors with
//                edge epochs and counters
//   keys         compute_public_point_with_evm_eip712 (Q8) equals noble and the
//                k256 helper; evm_eip712_address equals keccak256(x || y)[12..]
//                and refuses the point at infinity in both encodings
//   signatures   the wallet form r || s || v: parsing, refusals, the high-S
//                twin, EIP-191 digests, point recovery
//   blind        enrolment: the request signed twice, the sign-twice check (a
//                hedged wallet refused), the blind equal to derive_blind and to
//                SHA-256 of the specified preimage, the recovered point equal
//                to the wallet's key, a wallet that lies about its address
//                refused, per-index and per-network separation
//   roster       record round trip; a record whose address is not its point's
//                refused; restore finds accounts by testing entries
//   codec        (S4E) the frozen vectors src/tests/vectors/evm-eip712-v1.json,
//                whose hashes viem computed: for every vector the client
//                codec rebuilds the same typed data, and its digest, the
//                contract's struct hash, domain separator and digest all equal
//                the frozen ones; the type strings equal viem's encodeType;
//                every negative vector is refused by each layer it names
//                (client codec, generated JavaScript of the pure circuits);
//                the descriptor derivations equal descriptors.ts; the no-blob
//                classification of every signed member
//
// The independent check against viem lives in evm-eip712-viem.ts (viem is
// not a dependency of this package). Writes
// $EVIDENCE_DIR/evm-eip712-offline.json when EVIDENCE_DIR is set; never writes
// into the repository.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { pureCircuits } from '../wallet/contract.js';
import { padTag, evmAddressOf, evmChecksumAddress } from '../wallet/descriptors.js';
import { blindMessageBytes } from '../wallet/blind.js';
import {
  EVM_EIP712_PRIMARY_TYPES, EVM_EIP712_DESCRIPTOR_TYPES, typedDataDigest, typeString, siteLabelText, toHex,
} from '../wallet/evm-eip712-codec.js';
import { typedDataOf, contractStructHash, NEGATIVES, descriptorInput, granteeInput, VECTOR_FILE, type VectorInput } from './evm-eip712-vectors.js';
import {
  EvmEip712Device, EvmEip712Grantee, SoftwareEvmWallet, enrolEvmBlind, enrolEvmGranteeBlind, solArg, highSTwin, parseEvmSignature, personalMessageDigest,
  recoverEvmPoint, restoreEvmDevices, serialiseEvmSignature, SECP256K1_ORDER,
  type EvmWallet,
} from '../wallet/signer-evm-eip712.js';

const SEED = 'aa00067/e/s2/evm-eip712-offline/v1';
let ctr = 0;
const rnd = (n: number): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
const sha = (...p: Uint8Array[]) => { const h = createHash('sha256'); for (const x of p) h.update(x); return new Uint8Array(h.digest()); };
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const eq = (a: Uint8Array, b: Uint8Array) => Buffer.from(a).equals(Buffer.from(b));
const le = (v: bigint, w: number) => { const o = new Uint8Array(w); let x = v; for (let i = 0; i < w; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const be = (v: bigint, w = 32) => { const o = new Uint8Array(w); let x = v; for (let i = w - 1; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const beInt = (b: Uint8Array) => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const scalar = () => { for (;;) { const k = beInt(rnd(32)); if (k > 0n && k < SECP256K1_ORDER) return k; } };

const tally: Record<string, { pass: number; refused: number }> = {};
const ok = (k: string, n = 1) => { (tally[k] ??= { pass: 0, refused: 0 }).pass += n; };
const refused = (k: string, f: () => unknown, re: RegExp, why: string) => {
  assert.throws(f, re, `${k}: must refuse ${why}`);
  (tally[k] ??= { pass: 0, refused: 0 }).refused++;
};
const refusedAsync = async (k: string, f: () => Promise<unknown>, re: RegExp, why: string) => {
  await assert.rejects(f, re, `${k}: must refuse ${why}`);
  (tally[k] ??= { pass: 0, refused: 0 }).refused++;
};
const pc = pureCircuits as any;
const vectors: Record<string, unknown[]> = {};

// ── Recipes ──────────────────────────────────────────────────────────────────

const DEVICE_TAG = padTag('midnight:account:device:evm:v1');
const BOOT_TAG = padTag('midnight:account:boot:evm:v1');
const GRANT_ID_TAG = padTag('midnight:account:grant:id:evm:v1');
const BLIND_TAG = padTag('midnight:account:blind:evm:v1');
assert.ok(eq(pc.device_tag_evm_eip712(), DEVICE_TAG) && eq(pc.boot_tag_evm_eip712(), BOOT_TAG)
  && eq(pc.grant_id_tag_evm_eip712(), GRANT_ID_TAG) && eq(pc.blind_tag_evm_eip712(), BLIND_TAG), 'the arm hashes the registered evm:v1 tags');
ok('tags', 4);

const EDGE_EPOCHS = [0n, 1n, 0xffffffffn];
const EDGE_COUNTERS = [0n, 1n, 255n, 256n, 0xffffffffffffffffn];
vectors.entry = []; vectors.boot = []; vectors.grantId = [];
for (let i = 0; i < 24; i++) {
  const A = rnd(32), address = rnd(20), blind = rnd(32), salt = rnd(32), originHash = rnd(32);
  const epoch = i < EDGE_EPOCHS.length ? EDGE_EPOCHS[i] : beInt(rnd(4));
  const counter = i < EDGE_COUNTERS.length ? EDGE_COUNTERS[i] : beInt(rnd(8));
  const slot = BigInt(rnd(1)[0]);
  const entry = pc.derive_device_entry_with_evm_eip712({ bytes: A }, address, blind, epoch, counter);
  assert.ok(eq(entry, sha(DEVICE_TAG, A, address, blind, le(epoch, 4), le(counter, 8))), 'entry == SHA-256 of its preimage');
  assert.ok(eq(entry, pc.derive_descriptor_entry_w52(DEVICE_TAG, { bytes: A }, address, blind, epoch, counter)), 'entry == the module');
  const boot = pc.derive_boot_commitment_with_evm_eip712(salt, address, blind);
  assert.ok(eq(boot, sha(BOOT_TAG, salt, address, blind)), 'boot == SHA-256 of its preimage');
  assert.ok(eq(boot, pc.derive_descriptor_boot_w52(BOOT_TAG, salt, address, blind)), 'boot == the module');
  const gid = pc.derive_grant_id_with_evm_eip712({ bytes: A }, address, blind, originHash, slot);
  assert.ok(eq(gid, sha(GRANT_ID_TAG, A, address, blind, originHash, le(slot, 1))), 'grant id == SHA-256 of its preimage');
  assert.ok(eq(gid, pc.derive_descriptor_grant_id_w52(GRANT_ID_TAG, { bytes: A }, address, blind, originHash, slot)), 'grant id == the module');
  if (i < 3) {
    vectors.entry.push({ account: hex(A), address: hex(address), blind: hex(blind), epoch: String(epoch), counter: String(counter), entry: hex(entry) });
    vectors.boot.push({ salt: hex(salt), address: hex(address), blind: hex(blind), boot: hex(boot) });
    vectors.grantId.push({ account: hex(A), address: hex(address), blind: hex(blind), originHash: hex(originHash), slot: String(slot), grantId: hex(gid) });
  }
  ok('recipes', 3);
}
{
  // The blind is load-bearing: the same address under another blind, account,
  // epoch or counter gives another entry.
  const A = rnd(32), address = rnd(20), blind = rnd(32);
  const base = pc.derive_device_entry_with_evm_eip712({ bytes: A }, address, blind, 0n, 0n);
  for (const other of [
    pc.derive_device_entry_with_evm_eip712({ bytes: A }, address, rnd(32), 0n, 0n),
    pc.derive_device_entry_with_evm_eip712({ bytes: rnd(32) }, address, blind, 0n, 0n),
    pc.derive_device_entry_with_evm_eip712({ bytes: A }, address, blind, 1n, 0n),
    pc.derive_device_entry_with_evm_eip712({ bytes: A }, address, blind, 0n, 1n),
    pc.derive_device_entry_with_evm_eip712({ bytes: A }, rnd(20), blind, 0n, 0n),
  ]) assert.ok(!eq(base, other));
  ok('recipes', 5);
}
console.log(`  ✓ recipes: entry, boot and grant id == the module's w52 circuits == SHA-256 of the specified preimage (${tally.recipes.pass} checks)`);

// ── Keys ─────────────────────────────────────────────────────────────────────

const G = secp256k1.Point.BASE;
vectors.keys = [];
for (const k of [1n, 2n, SECP256K1_ORDER - 1n, ...Array.from({ length: 21 }, scalar)]) {
  const pt = pc.compute_public_point_with_evm_eip712(k);
  const ref = G.multiply(k).toAffine();
  assert.equal(pt.x, ref.x); assert.equal(pt.y, ref.y); assert.equal(pt.identity, false);
  const k256 = pc.compute_public_point_with_k256(k);
  assert.equal(k256.x, pt.x); assert.equal(k256.y, pt.y);
  const addr = pc.evm_eip712_address(pt);
  const refAddr = keccak_256(new Uint8Array([...be(ref.x), ...be(ref.y)])).subarray(12);
  assert.ok(eq(addr, refAddr), 'evm_eip712_address == keccak256(x || y)[12..]');
  assert.ok(eq(addr, evmAddressOf(ref)));
  if (vectors.keys.length < 4) vectors.keys.push({ scalar: k.toString(16), x: ref.x.toString(16), y: ref.y.toString(16), address: evmChecksumAddress(addr) });
  ok('keys', 4);
}
assert.equal(evmChecksumAddress(pc.evm_eip712_address(pc.compute_public_point_with_evm_eip712(1n))), '0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf');
{
  // The point at infinity, in both encodings, never yields an address.
  const flagged = pc.compute_public_point_with_evm_eip712(0n);
  assert.equal(flagged.identity, true, 'scalar 0 gives the flagged identity');
  refused('keys', () => pc.evm_eip712_address(flagged), /point at infinity|identity|failed assert/i, 'the flagged identity {0, 0, identity}');
  refused('keys', () => pc.evm_eip712_address({ x: 0n, y: 0n, identity: false }), /point at infinity|identity|not a valid|failed assert|curve/i, 'the unflagged identity {0, 0, not identity}');
  refused('keys', () => new EvmEip712Device({ x: 0n, y: 0n, identity: false } as any, rnd(32), 'undeployed', 0n), /point at infinity/, 'a device at infinity (client)');
  refused('keys', () => new EvmEip712Device({ x: 1n, y: 1n, identity: false } as any, rnd(32), 'undeployed', 0n), /not on curve|invalid|bad point/i, 'an off-curve device point (client)');
}
console.log(`  ✓ keys: Q8 helper == noble == the k256 helper; address == keccak256(x || y)[12..]; ${tally.keys.refused} degenerate keys refused`);

// ── Signatures ───────────────────────────────────────────────────────────────

{
  const w = new SoftwareEvmWallet(scalar());
  const digest = rnd(32);
  const sig = w.signDigest(digest);
  const p = parseEvmSignature(sig);
  assert.ok(p.s <= SECP256K1_ORDER / 2n, 'the software wallet signs low-S');
  assert.ok(eq(serialiseEvmSignature(p), sig));
  const rec = recoverEvmPoint(digest, p);
  assert.equal(rec.x, w.pk.x); assert.equal(rec.y, w.pk.y);
  const twin = highSTwin(p);
  assert.ok(twin.s > SECP256K1_ORDER / 2n);
  const rec2 = recoverEvmPoint(digest, twin);
  assert.equal(rec2.x, w.pk.x); assert.equal(rec2.y, w.pk.y);
  assert.ok(secp256k1.verify(new secp256k1.Signature(twin.r, twin.s).toBytes(), digest, secp256k1.Point.fromAffine(w.pk).toBytes(), { prehash: false, lowS: false }), 'the high-S twin verifies');
  ok('signatures', 5);
  const r = be(p.r), s = be(p.s);
  refused('signatures', () => parseEvmSignature(new Uint8Array([...be(0n), ...s, 27])), /r outside/, 'r = 0');
  refused('signatures', () => parseEvmSignature(new Uint8Array([...r, ...be(0n), 27])), /s outside/, 's = 0');
  refused('signatures', () => parseEvmSignature(new Uint8Array([...be(SECP256K1_ORDER), ...s, 27])), /r outside/, 'r = n');
  refused('signatures', () => parseEvmSignature(new Uint8Array([...r, ...be(SECP256K1_ORDER), 27])), /s outside/, 's = n');
  refused('signatures', () => parseEvmSignature(new Uint8Array([...r, ...s, 29])), /v must be/, 'v = 29');
  refused('signatures', () => parseEvmSignature(sig.subarray(0, 64)), /65 bytes/, 'the 64-byte form');
  // EIP-191: the prefix carries the decimal length of the message.
  const msg = new TextEncoder().encode('Midnight Passport');
  assert.ok(eq(personalMessageDigest(msg), keccak_256(new Uint8Array([...new TextEncoder().encode('\x19Ethereum Signed Message:\n17'), ...msg]))));
  ok('signatures');
}
console.log(`  ✓ signatures: wallet form, low-S signer, high-S twin recovers and verifies, EIP-191 digest; ${tally.signatures.refused} malformed signatures refused`);

// ── Blind enrolment ──────────────────────────────────────────────────────────

vectors.blind = [];
{
  const w = new SoftwareEvmWallet(1n);
  const e = await enrolEvmBlind(w, 'undeployed', 0);
  assert.ok(eq(e.signatures[0], e.signatures[1]), 'RFC 6979: the two signatures are equal');
  assert.ok(eq(e.blind, sha(BLIND_TAG, e.canonical)), 'blind == SHA-256(pad32(blind tag) || low-S r || s)');
  assert.ok(eq(e.blind, pc.derive_blind(BLIND_TAG, e.canonical)), 'blind == derive_blind');
  assert.equal(e.pk.x, w.pk.x); assert.equal(e.pk.y, w.pk.y);
  assert.ok(eq(e.address, w.addressBytes));
  const msg = blindMessageBytes({ scheme: 'evm_eip712', network: 'undeployed', identity: w.addressBytes, accountIndex: 0 });
  assert.ok(eq(e.message, msg));
  vectors.blind.push({ scalar: '1', network: 'undeployed', accountIndex: '0', message: new TextDecoder().decode(msg),
    eip191Digest: hex(personalMessageDigest(msg)), signature: hex(e.signatures[0]), canonical: hex(e.canonical), blind: hex(e.blind) });
  ok('blind', 5);
  const e1 = await enrolEvmBlind(w, 'undeployed', 1);
  const ePreview = await enrolEvmBlind(w, 'preview', 0);
  assert.ok(!eq(e1.blind, e.blind) && !eq(ePreview.blind, e.blind) && !eq(e1.blind, ePreview.blind), 'one blind per (network, index)');
  vectors.blind.push({ scalar: '1', network: 'undeployed', accountIndex: '1', blind: hex(e1.blind) }, { scalar: '1', network: 'preview', accountIndex: '0', blind: hex(ePreview.blind) });
  ok('blind', 1);
  // A high-S signature of the request gives the same blind (canonical form).
  const twin = serialiseEvmSignature(highSTwin(parseEvmSignature(e.signatures[0])));
  const viaTwin: EvmWallet = { address: () => w.address(), personalSign: async () => twin, signTypedData: () => { throw new Error('unused'); } };
  assert.ok(eq((await enrolEvmBlind(viaTwin, 'undeployed', 0)).blind, e.blind), 'the high-S twin gives the same blind');
  ok('blind');
  await refusedAsync('blind', () => enrolEvmBlind(new SoftwareEvmWallet(7n, true), 'undeployed', 0), /not deterministic/, 'a hedged (non-deterministic) wallet');
  const liar: EvmWallet = { address: async () => new SoftwareEvmWallet(2n).addressBytes, personalSign: (m) => w.personalSign(m), signTypedData: () => { throw new Error('unused'); } };
  await refusedAsync('blind', () => enrolEvmBlind(liar, 'undeployed', 0), /does not recover to the wallet address/, 'a wallet whose signature is not its address');
  await refusedAsync('blind', () => enrolEvmBlind(w, 'Undeployed', 0), /network name/, 'an upper-case network name');
  await refusedAsync('blind', () => enrolEvmBlind(w, 'undeployed', -1), /0 to 4294967295/, 'a negative account index');
  // (Q39) as a grantee the wallet derives its blind from the grantee request
  // for the issuing account: never one of its device blinds, one per issuer
  const deviceBlinds = await Promise.all([0, 1, 2, 3].map(async (i) => hex((await enrolEvmBlind(w, 'undeployed', i)).blind)));
  const issuers = [rnd(32), rnd(32)];
  const granteeBlinds = await Promise.all(issuers.map(async (a) => hex((await enrolEvmGranteeBlind(w, 'undeployed', a)).blind)));
  assert.ok(granteeBlinds.every((b) => !deviceBlinds.includes(b)), 'a grantee blind is never a device blind');
  assert.notEqual(granteeBlinds[0], granteeBlinds[1], 'two issuing accounts give two grantee blinds');
  const g0 = await EvmEip712Grantee.enrol(w, 'undeployed', issuers[0], new Uint8Array(32).fill(0x41), 0n);
  assert.equal(hex(g0.blind), granteeBlinds[0], 'EvmEip712Grantee.enrol uses the grantee request');
  assert.equal(hex((await enrolEvmGranteeBlind(w, 'preview', issuers[0])).blind) === granteeBlinds[0], false, 'and names the network');
  ok('blind', 4);
  await refusedAsync('blind', () => enrolEvmGranteeBlind(w, 'undeployed', new Uint8Array(32)), /issuing account address is not zero/, 'a grantee request for the zero account');
}
console.log(`  ✓ blind: deterministic, == derive_blind == SHA-256, recovered point == the wallet key, per index and network; grantee blinds per issuing account, never a device blind (Q39); ${tally.blind.refused} bad enrolments refused`);

// ── Roster and restore ───────────────────────────────────────────────────────

{
  const w = new SoftwareEvmWallet(scalar());
  const d = await EvmEip712Device.enrol(w, 'undeployed', 0);
  const rec = d.toRecord();
  const back = EvmEip712Device.fromRecord(JSON.parse(JSON.stringify(rec)));
  assert.ok(eq(back.address, d.address) && eq(back.blind, d.blind) && back.accountIndex === 0n && back.network === 'undeployed');
  assert.equal(rec.address, evmChecksumAddress(w.addressBytes));
  ok('roster');
  const other = new SoftwareEvmWallet(scalar());
  refused('roster', () => EvmEip712Device.fromRecord({ ...rec, address: evmChecksumAddress(other.addressBytes) }), /not the point's address/, 'a record whose address is not its point\'s');
  refused('roster', () => EvmEip712Device.fromRecord({ ...rec, blind: 'zz' }), /hex/, 'a malformed blind');

  // Restore: index 0 on account A at counter 3, index 2 on account B at
  // counter 0; index 1 and every other account match nothing.
  const A = rnd(32), B = rnd(32), C = rnd(32);
  const d0 = await EvmEip712Device.enrol(w, 'undeployed', 0);
  const d2 = await EvmEip712Device.enrol(w, 'undeployed', 2);
  const setA = new Set([hex(d0.entryAt(A, 0n, 3n)), hex(rnd(32))]);
  const setB = new Set([hex(d2.entryAt(B, 0n, 0n))]);
  const setC = new Set([hex(d0.entryAt(A, 0n, 0n))]); // an entry of A planted in C matches nothing in C
  const found = await restoreEvmDevices(w, 'undeployed', [
    { address: A, epoch: 0n, isMember: (e) => setA.has(hex(e)) },
    { address: B, epoch: 0n, isMember: (e) => setB.has(hex(e)) },
    { address: C, epoch: 0n, isMember: (e) => setC.has(hex(e)) },
  ], { maxIndex: 3, maxCounter: 8n });
  assert.deepEqual(found.map((f) => [f.accountIndex, hex(f.account), f.counter]), [[0n, hex(A), 3n], [2n, hex(B), 0n]]);
  ok('roster', 2);
}
console.log(`  ✓ roster: record round trip; restore finds index 0 (counter 3) and index 2 (counter 0) only; ${tally.roster.refused} bad records refused`);

// ── Codec: the frozen vectors (S4E) ──────────────────────────────────────────

const FROZEN = JSON.parse(fs.readFileSync(new URL(`./vectors/${VECTOR_FILE}`, import.meta.url), 'utf8'));
{
  assert.match(FROZEN.hashesBy, /^viem 2\./, 'the frozen hashes come from viem');
  const strip = (v: any) => { const { typedData, encodeType, domainSeparator, structHash, digest, ...input } = v; return input as VectorInput; };
  const seen = new Set<string>();
  for (const v of FROZEN.vectors) {
    const input = strip(v);
    const td = typedDataOf(input);
    assert.deepEqual(JSON.parse(JSON.stringify(td)), v.typedData, `${v.name}: the codec rebuilds the frozen typed data`);
    assert.equal(toHex(typedDataDigest(td)), v.digest, `${v.name}: client digest`);
    const sh = contractStructHash(pc, input);
    assert.equal(toHex(sh), v.structHash, `${v.name}: contract struct hash`);
    const acct = Buffer.from(v.frame.account, 'hex');
    assert.equal(toHex(pc.evm_eip712_domain_separator(acct)), v.domainSeparator, `${v.name}: contract domain separator`);
    assert.equal(toHex(pc.evm_eip712_digest(acct, sh)), v.digest, `${v.name}: contract digest`);
    assert.equal(v.typedData.domain.verifyingContract.toLowerCase(), '0x' + hex(pc.evm_eip712_verifying_contract(acct)), `${v.name}: verifyingContract`);
    seen.add(v.typedData.primaryType + (Object.keys(v.typedData.types).find((t) => t in EVM_EIP712_DESCRIPTOR_TYPES) ?? ''));
    ok('codec vectors');
  }
  // every primary type, and every descriptor-taking type with all five schemes
  const expected = Object.keys(EVM_EIP712_PRIMARY_TYPES).flatMap((p) => {
    const nested = EVM_EIP712_PRIMARY_TYPES[p].find(([, t]) => t.startsWith('<'));
    if (!nested) return [p];
    return Object.keys(EVM_EIP712_DESCRIPTOR_TYPES).filter((t) => t.endsWith(nested[1] === '<Device>' ? 'Device' : 'Grantee')).map((t) => p + t);
  });
  assert.deepEqual([...seen].sort(), expected.sort(), 'the vectors cover all 16 primary types and every descriptor scheme');
  for (const [k, str] of Object.entries(FROZEN.typeStrings as Record<string, string>)) {
    const [p, n] = k.split('/');
    assert.equal(typeString(p, n), str, `${k}: type string == viem encodeType`);
    ok('type strings');
  }
  assert.equal(Object.keys(FROZEN.typeStrings).length, 32);
  // dynamic members: entries with leading zero bytes and all-zero bytes
  const dyn = FROZEN.vectors.filter((v: any) => /append_inbox|publish_recovery|as_grantee/.test(v.name));
  assert.ok(dyn.some((v: any) => /^0x00/.test(v.typedData.message.entry ?? v.typedData.message.wrap ?? v.typedData.message.changeEntry ?? '')), 'a dynamic member with leading zero bytes');
  assert.ok(dyn.some((v: any) => /^0x(00)+$/.test(v.typedData.message.entry ?? v.typedData.message.wrap ?? '')), 'an all-zero dynamic member');
  ok('codec vectors', 2);
}
const negativeResults: { name: string; refusedBy: string[]; client?: string; runtime?: string }[] = [];
for (const n of FROZEN.negatives) {
  const r: any = { name: n.name, refusedBy: n.refusedBy };
  if (n.refusedBy.includes('client')) {
    assert.throws(() => typedDataOf(n.input), (e: any) => { r.client = String(e?.message ?? e); return true; }, `${n.name}: the client codec must refuse`);
  }
  if (n.refusedBy.includes('runtime')) {
    assert.throws(() => contractStructHash(pc, n.input), (e: any) => { r.runtime = String(e?.message ?? e); return true; }, `${n.name}: the contract's pure circuit must refuse`);
  }
  negativeResults.push(r);
  (tally['codec negatives'] ??= { pass: 0, refused: 0 }).refused++;
}
assert.equal(negativeResults.length, NEGATIVES.length);
// The descriptor derivations of the codec module equal the shared module's
// width-class circuits (S1 checked those against upstream and SHA-256). The
// frozen keys are random bytes, so descriptors.ts's strict decoders are not
// used here; those decoders are covered by wallet-arms-client-offline.
{
  for (const v of FROZEN.vectors.filter((x: any) => /^(add|remove)_device\//.test(x.name))) {
    const d = descriptorInput(v.args.descriptor);
    const A = { bytes: rnd(32) };
    const s = v.args.descriptor.scheme;
    const pt = solArg(d);
    for (const [e, c] of [[0n, 0n], [3n, 9n]] as [bigint, bigint][]) {
      const [sk, se] = pc.evm_eip712_sol_device_target(A, d, pt, e, c);
      const want = s === 'evm_eip712' ? pc.derive_descriptor_entry_w52(d.tag, A, d.address, d.key2, e, c)
        : s === 'k256' ? pc.derive_descriptor_entry_w65(d.tag, A, d.key, d.key2, d.envelope, e, c)
        : s === 'p256' ? pc.derive_descriptor_entry_w117(d.tag, A, d.key, d.key2, d.rp_id_hash, d.origin, e, c)
        : s === 'sol_ed25519' ? pc.derive_descriptor_entry_ed25519(d.tag, A, pt, d.key2, e, c)[1]
        : pc.derive_descriptor_entry_w64(d.tag, A, d.key, d.key2, e, c);
      assert.ok(eq(pc.evm_eip712_descriptor_entry(A, d, se, e, c), want), `${v.name}: descriptor entry == the class circuit`);
      // (Q37) a Solana target's shown key is the key the ed25519 class derived from the point
      if (s === 'sol_ed25519') assert.ok(eq(sk, d.key) && eq(sk, pc.encode_public_key_with_sol_ed25519(pt)), `${v.name}: the shown Solana key is the point's encoding`);
    }
    if (s === 'evm_eip712') assert.ok(eq(pc.evm_eip712_descriptor_entry(A, d, new Uint8Array(32), 0n, 0n), pc.derive_device_entry_with_evm_eip712(A, d.address, d.key2, 0n, 0n)));
    ok('descriptor derivations');
  }
  for (const v of FROZEN.vectors.filter((x: any) => /^(issue|revoke)_grant\//.test(x.name))) {
    const g = granteeInput(v.args.grantee);
    const A = { bytes: rnd(32) };
    const oh = pc.evm_eip712_grantee_origin_hash(g);
    const s = v.args.grantee.scheme;
    if (s === 'evm_eip712' || s === 'sol_ed25519') assert.ok(eq(oh, pc.derive_grant_origin_hash_label(g.label)));
    else if (s === 'p256') assert.ok(eq(oh, pc.derive_grant_origin_hash_origin(g.origin)));
    else assert.ok(eq(oh, g.origin_hash));
    const gpt = solArg(g);
    const [gsk, gsi] = pc.evm_eip712_sol_grantee_target(A, g, oh, gpt);
    const want = s === 'evm_eip712' ? pc.derive_descriptor_grant_id_w52(g.tag, A, g.address, g.key2, oh, g.slot)
      : s === 'k256' ? pc.derive_descriptor_grant_id_w65(g.tag, A, g.key, g.key2, g.envelope, oh, g.slot)
      : s === 'sol_ed25519' ? pc.derive_descriptor_grant_id_ed25519(g.tag, A, gpt, g.key2, oh, g.slot)[1]
      : pc.derive_descriptor_grant_id_w64(g.tag, A, g.key, g.key2, oh, g.slot);
    assert.ok(eq(pc.evm_eip712_grantee_grant_id(A, g, oh, gsi), want), `${v.name}: grantee grant id == the class circuit`);
    if (s === 'sol_ed25519') assert.ok(eq(gsk, g.key), `${v.name}: the shown Solana grantee key is the point's encoding`);
    ok('descriptor derivations');
  }
  // the site label as shown == the contract's rendering
  for (const t of ['Midnight Night Market', 'x', 'A'.repeat(32), 'a b c']) {
    const l = new Uint8Array(32); l.set(new TextEncoder().encode(t));
    assert.ok(eq(pc.evm_eip712_site_label_hash(l), keccak_256(new TextEncoder().encode(siteLabelText(l)))));
    assert.equal(siteLabelText(l).length, 32);
    ok('descriptor derivations');
  }
}
// The no-blob classification (FR-004, SC-006): every signed member is a value
// shown in full, and the only hash-like members are the four labelled ones.
const CLASS: Record<string, string> = {
  account: 'identifier', device: 'key', grantee: 'key', wallet: 'key', publicKey: 'key', x: 'key', y: 'key', recoveryKeyX: 'key', recoveryKeyY: 'key',
  authNonce: 'value', issuedAt: 'value', grantNonce: 'value', slot: 'value', amount: 'value', color: 'identifier', recipient: 'identifier',
  recipientContract: 'identifier', coinNonce: 'witness', coinValue: 'witness', coinMerkleIndex: 'witness', change: 'witness (derived)',
  entry: 'ciphertext (full bytes) / Q20 literal entry', changeEntry: 'ciphertext (full bytes)', newKey: 'value', effect: 'circuit-fixed line',
  newDevice: 'descriptor', target: 'descriptor', targetEpoch: 'value', targetCounter: 'value', scheme: 'circuit-fixed tag text', envelope: 'text label (a circuit constant selected by the value, Q35)',
  origin: 'text', siteLabel: 'text', withdrawUnshielded: 'value', withdrawShielded: 'value', withdrawShieldedToContract: 'value', read: 'value',
  recipientKind: 'text label (a circuit constant selected by the value, Q35)', maxCoinValue: 'value', perCallCap: 'value', cap: 'value', expiresAt: 'value', readKey: 'key (preimage of read_pk_hash)',
  windowLength: 'value', windowCap: 'value', callerPinned: 'value', caller: 'identifier', sessionNonce: 'value', phi1: 'value', phi2: 'value',
  phi3: 'value', phi4: 'value', phiLength: 'value', wrap: 'ciphertext (full bytes)', encryptionKey: 'key',
  privacySalt: 'LABELLED (Q21: a target device\'s blind)', passkeyRpHash: 'LABELLED (Q21: the passkey RP hash)', siteLabelHash: 'LABELLED (Q17: a k256/jubjub grantee\'s origin_hash)',
};
{
  const labelled = new Set<string>();
  for (const [t, fields] of [...Object.entries(EVM_EIP712_PRIMARY_TYPES).map(([k, v]) => [k, v.map(([n]) => n)] as [string, string[]]),
                            ...Object.entries(EVM_EIP712_DESCRIPTOR_TYPES).map(([k, v]) => [k, v.map((x) => x.name)] as [string, string[]])]) {
    for (const n of fields) {
      assert.ok(n in CLASS, `${t}.${n} has no no-blob classification`);
      if (CLASS[n].startsWith('LABELLED')) labelled.add(n);
      if (n === 'entry' && t === 'RemoveUnknownDevice') labelled.add('RemoveUnknownDevice.entry');
    }
  }
  assert.deepEqual([...labelled].sort(), ['RemoveUnknownDevice.entry', 'passkeyRpHash', 'privacySalt', 'siteLabelHash'], 'exactly the four labelled values');
  assert.equal(EVM_EIP712_PRIMARY_TYPES.RemoveUnknownDevice.find(([n]) => n === 'entry')![1], 'bytes32');
  ok('no-blob review');
}
console.log(`  ✓ codec: ${tally['codec vectors'].pass} frozen-vector checks (contract == client == viem-frozen), ${tally['type strings'].pass} type strings == viem; ${tally['codec negatives'].refused} negatives refused by every named layer; descriptor derivations == the width-class circuits (${tally['descriptor derivations'].pass}); no-blob: only the four labelled values`);

// ── G2E-2: the seam's call sites (a static check of the arm's source) ─────
//
// The shared core evm_eip712_verify_and_roll takes the address and the
// struct hash from its callers, and the module's frame builders take the
// frame values as arguments; only the call sites make them the derived
// address, kernel.self() and the ledger's auth_nonce (G1E-1). This reads
// contracts/account-evm-eip712.compact as text and holds every call site to
// that shape, so a future export that calls the core or a frame builder
// itself fails here.
{
  // (EVM_EIP712_ARM_SOURCE: another copy of the file, for the check's own mutant runs)
  const src = fs.readFileSync(process.env.EVM_EIP712_ARM_SOURCE ?? new URL('../../contracts/account-evm-eip712.compact', import.meta.url), 'utf8')
    .replace(/\/\/[^\n]*/g, (m) => ' '.repeat(m.length));
  interface Circuit { name: string; exported: boolean; params: string; body: string }
  const circuits: Circuit[] = [];
  const head = /(export\s+)?circuit\s+([A-Za-z0-9_]+)\s*(<[^>]*>)?\s*\(/g;
  for (let m; (m = head.exec(src)); ) {
    let i = m.index + m[0].length, depth = 1;
    while (depth) { const c = src[i++]; if (c === '(') depth++; else if (c === ')') depth--; }
    const params = src.slice(m.index + m[0].length, i - 1);
    const open = src.indexOf('{', i);
    let j = open + 1; depth = 1;
    while (depth) { const c = src[j++]; if (c === '{') depth++; else if (c === '}') depth--; }
    circuits.push({ name: m[2], exported: Boolean(m[1]), params, body: src.slice(open + 1, j - 1) });
    head.lastIndex = j;
  }
  const byName = new Map(circuits.map((c) => [c.name, c]));
  const calls = (fn: string) => circuits.filter((c) => new RegExp(`\\b${fn}\\s*(<[^(]*>)?\\(`).test(c.body)).map((c) => c.name).sort();
  /** Top-level arguments of the first call of `fn` in `body`. */
  const argsOf = (body: string, fn: string): string[] => {
    const m = new RegExp(`\\b${fn}\\s*(<[\\s\\S]*?>)?\\(`).exec(body);
    assert.ok(m, `no call of ${fn}`);
    let i = m!.index + m![0].length, depth = 1, cur = '';
    const out: string[] = [];
    while (depth) {
      const c = body[i++];
      if ('([<{'.includes(c)) depth++;
      if (')]>}'.includes(c)) depth--;
      if (depth === 1 && c === ',') { out.push(cur.trim()); cur = ''; } else if (depth) cur += c;
    }
    if (cur.trim()) out.push(cur.trim());
    return out.map((x) => x.replace(/\s+/g, ' '));
  };
  const ENTRY = ['require_authorised_with_evm_eip712', 'require_authorised_with_evm_eip712_either', 'require_authorised_with_evm_eip712_bare'];
  const SEAMS = [...ENTRY, 'require_grant_with_evm_eip712'];
  const firstStatement = (c: Circuit) => c.body.trim().split(';')[0].replace(/\s+/g, ' ');
  // 1. the core: defined once, called exactly by the three device entry points
  assert.ok(byName.has('evm_eip712_verify_and_roll') && !byName.get('evm_eip712_verify_and_roll')!.exported, 'the core exists and is not exported');
  assert.deepEqual(calls('evm_eip712_verify_and_roll'), [...ENTRY].sort(), 'the core is called by the three device entry points only');
  for (const e of ENTRY) {
    const c = byName.get(e)!;
    assert.equal(firstStatement(c), 'const address = evm_eip712_address(auth.pk)', `${e} derives the address from the presented point first`);
    assert.equal((c.body.match(/\bevm_eip712_verify_and_roll\s*\(/g) ?? []).length, 1, `${e} calls the core once`);
    assert.deepEqual(argsOf(c.body, 'evm_eip712_verify_and_roll').slice(0, 2), ['auth', 'address'], `${e} hands the core the presented auth and the derived address`);
    for (const b of ['evm_eip712_device_struct', 'evm_eip712_device_struct_bare']) {
      for (const m of c.body.matchAll(new RegExp(`\\b${b}\\s*(<[^(]*>)?\\(`, 'g'))) {
        const a = argsOf(c.body.slice(m.index), b);
        assert.deepEqual(a.slice(1, 4), ['kernel.self().bytes', 'address', 'auth_nonce'], `${e}: the frame is kernel.self(), the derived address and the ledger auth_nonce`);
      }
    }
  }
  // 2. the frame builders: only the seams build frames
  assert.deepEqual([...new Set([...calls('evm_eip712_device_struct'), ...calls('evm_eip712_device_struct_bare')])].sort(), [...ENTRY].sort(), 'device frames are built only by the entry points');
  assert.deepEqual(calls('evm_eip712_grantee_struct'), ['require_grant_with_evm_eip712'], 'grantee frames are built only by the grant seam');
  {
    const g = byName.get('require_grant_with_evm_eip712')!;
    assert.equal(firstStatement(g), 'const address = evm_eip712_address(auth.pk)', 'the grant seam derives the grantee address first');
    assert.deepEqual(argsOf(g.body, 'evm_eip712_grantee_struct').slice(1, 7), ['kernel.self().bytes', 'address', 'label', 'slot', 'g.issued_at', 'g.nonce'],
      'the grantee frame is kernel.self(), the derived address, the label and slot of the grant id, and the record\'s issued_at and nonce');
    assert.ok(/derive_grant_id_with_evm_eip712\(kernel\.self\(\), address, auth\.blind/.test(g.body.replace(/\s+/g, ' ')), 'the grant id is derived from the derived address');
  }
  // 3. every gated export goes through exactly one seam; nothing else is gated
  const gated = circuits.filter((c) => c.exported && /\bauth\s*:/.test(c.params));
  assert.equal(gated.length, 15, '15 gated exports');
  for (const c of gated) {
    const used = SEAMS.filter((s) => new RegExp(`\\b${s}\\s*(<[\\s\\S]*?>)?\\(`).test(c.body));
    assert.equal(used.length, 1, `${c.name} calls exactly one seam (${used.join(', ')})`);
    assert.equal((c.body.match(new RegExp(`\\b${used[0]}\\s*(<[\\s\\S]*?>)?\\(`, 'g')) ?? []).length, 1, `${c.name} calls its seam once`);
    assert.ok(!/\bevm_eip712_(verify_and_roll|device_struct|device_struct_bare|grantee_struct)\s*(<[^(]*>)?\(/.test(c.body), `${c.name} builds no frame and calls no core itself`);
  }
  // 4. each grantee twin hands the seam the values its signed tail shows
  const TWIN_OP: Record<string, string> = { withdraw_unshielded_with_grant_evm_eip712: '1', withdraw_shielded_with_grant_evm_eip712: '2', withdraw_shielded_to_contract_with_grant_evm_eip712: '3' };
  for (const [twin, op] of Object.entries(TWIN_OP)) {
    const c = byName.get(twin)!;
    const parts = argsOf(c.body, `evm_eip712_parts_${twin.replace('_with_grant_evm_eip712', '')}_as_grantee`);
    const seam = argsOf(c.body, 'require_grant_with_evm_eip712');
    // seam: auth, label, slot, scope_salt, recipient_kind, pinned_recipient, max_coin_value, spent_prev, op, obj_color, amount, recipient_bytes, type_hash, tail
    assert.equal(seam[8], op, `${twin}: the op constant`);
    assert.equal(seam[10], parts[1], `${twin}: the amount the seam checks is the signed one`);
    assert.equal(seam[11], parts[2], `${twin}: the recipient the seam checks is the signed one`);
    if (op === '1') assert.equal(seam[9], parts[0], `${twin}: the colour the seam checks is the signed one`);
    else {
      assert.equal(seam[9], 'coin.color', `${twin}: the scope colour is the spent coin's`);
      assert.ok(/assert\(coin\.color == color,/.test(c.body.replace(/\s+/g, ' ')) && parts[0] === 'color', `${twin}: coin.color == color (FR-010), so the scope colour is the signed one`);
      assert.deepEqual(parts.slice(5, 8), ['coin.nonce', 'coin.value', 'coin.mt_index'], `${twin}: the signed coin is the spent coin`);
    }
  }
  ok('seam call sites (G2E-2)', 1);
  console.log(`  ✓ seam call sites: the core called only by the 3 device entry points (each derives the address first; frame = kernel.self(), the derived address, auth_nonce); frames built only by the seams; 15 gated exports, each through exactly one seam; the 3 grantee twins hand the seam the signed colour, amount and recipient`);
}

const report = { suite: 'evm-eip712-offline', step: 'S2E+S4E', seed: SEED, ranAt: new Date().toISOString(), tally, vectors, frozen: { file: `src/tests/vectors/${VECTOR_FILE}`, vectors: FROZEN.vectors.length, negatives: negativeResults, hashesBy: FROZEN.hashesBy }, noBlob: CLASS, verdict: 'PASS' };
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'evm-eip712-offline.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log('\n◆ evm-eip712-offline: PASS');
