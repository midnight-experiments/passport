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
//
// The independent check against ethers lives in evm-eip712-ethers.ts (ethers
// is not a dependency of this package). Writes
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
  EvmEip712Device, SoftwareEvmWallet, enrolEvmBlind, highSTwin, parseEvmSignature, personalMessageDigest,
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

const DEVICE_TAG = padTag('midnight:account:device:evm:v2');
const BOOT_TAG = padTag('midnight:account:boot:evm:v2');
const GRANT_ID_TAG = padTag('midnight:account:grant:id:evm:v2');
const BLIND_TAG = padTag('midnight:account:blind:evm:v2');
assert.ok(eq(pc.device_tag_evm_eip712(), DEVICE_TAG) && eq(pc.boot_tag_evm_eip712(), BOOT_TAG)
  && eq(pc.grant_id_tag_evm_eip712(), GRANT_ID_TAG) && eq(pc.blind_tag_evm_eip712(), BLIND_TAG), 'the arm hashes the registered evm:v2 tags');
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
}
console.log(`  ✓ blind: deterministic, == derive_blind == SHA-256, recovered point == the wallet key, per index and network; ${tally.blind.refused} bad enrolments refused`);

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

const report = { suite: 'evm-eip712-offline', step: 'S2E', seed: SEED, ranAt: new Date().toISOString(), tally, vectors, verdict: 'PASS' };
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'evm-eip712-offline.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log('\n◆ evm-eip712-offline: PASS');
