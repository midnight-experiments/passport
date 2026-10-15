// Offline suite for the readable-arm client helpers: src/wallet/descriptors.ts
// (descriptor encoders and strict decoders) and src/wallet/blind.ts (the blind
// request message and the canonical signature forms).
//
//   tags         the client's tag tables equal the module's constants
//   parsers      EIP-55 addresses, base58 Solana keys with RFC 8032 strict
//                decoding (identity, small-order, mixed-order, non-canonical
//                and off-curve points refused), SEC1 secp256k1 and P-256 keys,
//                passkey policies (parent-domain RP accepted, a mismatched RP
//                refused), and JubJub points
//   encoders     every scheme and recipe, run through the probe, equals
//                upstream's own circuit (legacy schemes) or SHA-256 of the
//                specified preimage (new schemes); the decoder inverts the
//                encoder and refuses unknown tags, other recipes' tags, wrong
//                widths, and inadmissible keys
//   display      the shown lines, including the two labelled values
//   blind        golden request messages, input refusals, low-S EVM and
//                strict Ed25519 canonical forms, the sign-twice check against
//                a deterministic and a hedged signer, and derive_blind
//
// Writes $EVIDENCE_DIR/wallet-arms-client-offline.json when EVIDENCE_DIR is
// set; never writes into the repository.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { p256 } from '@noble/curves/nist.js';
import { ed25519, ED25519_TORSION_SUBGROUP } from '@noble/curves/ed25519.js';
import { jubjub } from '@noble/curves/misc.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { pureCircuits as probe } from '../../contracts/managed/probe-wallet-arms-base/contract/index.js';
import { pureCircuits as upstream } from '../wallet/contract.js';
import {
  DESCRIPTOR_SCHEMES, DESCRIPTOR_TAGS, BLIND_TAGS, GRANT_ORIGIN_TAG, PAYLOAD_WIDTH,
  padTag, tagOf, evmChecksumAddress, parseEvmAddress, evmAddressOf, base58Encode, base58Decode,
  parseSolanaPublicKey, parseK256Descriptor, parseP256Descriptor, parseJubjubPoint, evmDescriptor,
  solDescriptor, checkDescriptor, payloadParts, entryCall, bootCall, grantIdCall, derive, decodeDescriptor,
  describeDescriptor, grantOriginHash, grantLabel,
  type Descriptor, type DescriptorRecipe,
} from '../wallet/descriptors.js';
import {
  blindMessage, blindMessageBytes, canonicalEvmSignature, canonicalEd25519Signature,
  sameCanonicalSignature, deriveBlind, blindCall,
} from '../wallet/blind.js';

const SEED = 'aa00067/s1/wallet-arms-client-offline/v1';
let ctr = 0;
const rnd = (n: number): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
const sha = (...p: Uint8Array[]) => { const h = createHash('sha256'); for (const x of p) h.update(x); return new Uint8Array(h.digest()); };
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const unhex = (s: string) => new Uint8Array(Buffer.from(s.replace(/^0x/, ''), 'hex'));
const eq = (a: Uint8Array, b: Uint8Array) => Buffer.from(a).equals(Buffer.from(b));
const le = (v: bigint, w: number) => { const o = new Uint8Array(w); let x = v; for (let i = 0; i < w; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const bigLE = (b: Uint8Array) => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };
const ascii = (v: bigint[]) => String.fromCharCode(...v.map(Number));

const tally: Record<string, { pass: number; refused: number }> = {};
const ok = (k: string) => { (tally[k] ??= { pass: 0, refused: 0 }).pass++; };
const refused = (k: string, f: () => unknown, re: RegExp, why: string) => {
  assert.throws(f, re, `${k}: must refuse ${why}`);
  (tally[k] ??= { pass: 0, refused: 0 }).refused++;
};

// ── Tags ─────────────────────────────────────────────────────────────────────

const probeTag = (recipe: string, scheme: string): Uint8Array => (probe as any)[`${recipe.replace('-', '_')}_tag_${scheme}`]();
for (const recipe of Object.keys(DESCRIPTOR_TAGS) as DescriptorRecipe[]) {
  for (const scheme of DESCRIPTOR_SCHEMES) {
    assert.ok(eq(padTag(DESCRIPTOR_TAGS[recipe][scheme]), probeTag(recipe, scheme)), `${recipe}/${scheme} tag`);
    const t = tagOf(probeTag(recipe, scheme));
    assert.equal(t.recipe, recipe); assert.equal(t.scheme, scheme);
    ok('tags');
  }
}
assert.ok(eq(padTag(BLIND_TAGS.evm_eip712), probe.blind_tag_evm_eip712()));
assert.ok(eq(padTag(BLIND_TAGS.sol_ed25519), probe.blind_tag_sol_ed25519()));
assert.ok(eq(padTag(GRANT_ORIGIN_TAG), probe.grant_origin_tag()));
refused('tags', () => tagOf(padTag('midnight:account:device:ed:v1')), /unregistered tag/, 'an unregistered tag');
refused('tags', () => tagOf(new Uint8Array(32).fill(0x20).map((c, i) => 'midnight:account:device:v1'.charCodeAt(i) || c)), /unregistered tag/, 'a space-padded tag');
refused('tags', () => padTag('midnight:account:grant:id:evm:v22'), /exceeds 32 bytes/, 'a 33-byte tag');
console.log(`  ✓ tags: client tables equal the module's constants (${tally.tags.pass}); ${tally.tags.refused} malformed tags refused`);

// ── Parsers ──────────────────────────────────────────────────────────────────

// EIP-55 (the EIP's own examples).
for (const a of ['0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed', '0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359',
  '0xdbF03B407c01E7cD3CBea99509d93f8DDDC8C6FB', '0xD1220A0cf47c7B9Be7A2E6BA89F429762e7b9aDb']) {
  assert.equal(evmChecksumAddress(parseEvmAddress(a)), a);
  assert.equal(evmChecksumAddress(parseEvmAddress(a.toLowerCase())), a);
  assert.equal(evmChecksumAddress(parseEvmAddress('0x' + a.slice(2).toUpperCase())), a);
  ok('evm address');
}
assert.equal(evmChecksumAddress(evmAddressOf(secp256k1.Point.BASE.toAffine())), '0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf');
refused('evm address', () => parseEvmAddress('0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAeD'), /checksum/, 'a wrong checksum');
refused('evm address', () => parseEvmAddress('0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAe'), /40 hex/, '39 digits');
refused('evm address', () => parseEvmAddress('5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed'), /40 hex/, 'no 0x');
refused('evm address', () => parseEvmAddress('0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAeg'), /40 hex/, 'a non-hex digit');
refused('evm address', () => parseEvmAddress('0x' + '0'.repeat(40)), /zero address/, 'the zero address');

// Base58.
assert.equal(base58Encode(new Uint8Array(32)), '11111111111111111111111111111111');
assert.ok(eq(base58Decode('So11111111111111111111111111111111111111112', 32), unhex('069b8857feab8184fb687f634618c035dac439dc1aeb3b5598a0f00000000001')));
for (let i = 0; i < 32; i++) { const b = rnd(32); if (i % 4 === 0) b[0] = 0; assert.ok(eq(base58Decode(base58Encode(b), 32), b)); ok('base58'); }
refused('base58', () => base58Decode('0OIl', 32), /not base58/, 'characters outside the alphabet');
refused('base58', () => base58Decode('1' + base58Encode(rnd(32)), 32), /bytes, not 32/, 'a leading zero byte too many');
refused('base58', () => base58Decode('', 32), /not base58/, 'empty text');

// Solana keys: RFC 8032 section 7.1, test 1, and seeded keys.
const RFC8032_PK = 'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a';
assert.ok(eq(parseSolanaPublicKey(unhex(RFC8032_PK)), unhex(RFC8032_PK)));
for (let i = 0; i < 16; i++) {
  const pk = ed25519.getPublicKey(rnd(32));
  assert.ok(eq(parseSolanaPublicKey(base58Encode(pk)), pk));
  ok('solana key');
}
for (const t of ED25519_TORSION_SUBGROUP) refused('solana key', () => parseSolanaPublicKey(unhex(t)), /small order|canonical/, `torsion point ${t}`);
{
  const P = ed25519.Point.fromBytes(unhex(RFC8032_PK));
  const T = ed25519.Point.fromHex(ED25519_TORSION_SUBGROUP[1]);
  refused('solana key', () => parseSolanaPublicKey(P.add(T).toBytes()), /mixed order/, 'a mixed-order point');
  const P_ED = ed25519.Point.Fp.ORDER;
  refused('solana key', () => parseSolanaPublicKey(le(P_ED + 1n, 32)), /canonical/, 'y = p + 1 (a non-canonical identity)');
  const negZero = new Uint8Array(32); negZero[0] = 1; negZero[31] = 0x80;
  refused('solana key', () => parseSolanaPublicKey(negZero), /canonical|small order/, 'x = 0 with the sign bit set');
  let off: Uint8Array | undefined;
  for (let i = 0; !off; i++) { const c = rnd(32); c[31] &= 0x7f; try { ed25519.Point.fromBytes(c, false); } catch { off = c; } }
  refused('solana key', () => parseSolanaPublicKey(off!), /canonical Ed25519 point/, 'a y with no curve point');
  refused('solana key', () => parseSolanaPublicKey(unhex(RFC8032_PK).subarray(0, 31)), /32 bytes/, '31 bytes');
}

// secp256k1 keys.
{
  const pt = secp256k1.Point.BASE.multiply(0xc0ffeen);
  const { x, y } = pt.toAffine();
  for (const enc of [pt.toBytes(true), pt.toBytes(false)]) {
    const d = parseK256Descriptor(enc, 1);
    assert.equal(d.x, x); assert.equal(d.y, y); assert.equal(d.envelope, 1);
    ok('k256 key');
  }
  refused('k256 key', () => parseK256Descriptor({ x: 0n, y: 0n }, 0), /not a secp256k1 public key|infinity/, 'the point at infinity (coordinates 0, 0)');
  refused('k256 key', () => parseK256Descriptor({ x, y: y + 1n }, 0), /not a secp256k1 public key/, 'a point off the curve');
  refused('k256 key', () => parseK256Descriptor({ x: x + secp256k1.Point.Fp.ORDER, y }, 0), /not below p/, 'a coordinate not below p');
  refused('k256 key', () => parseK256Descriptor({ x, y }, 2), /unknown k256 envelope/, 'envelope 2');
}

// Passkeys: the RP ID may be a registrable parent of the origin's host.
{
  const pt = p256.Point.BASE.multiply(0xbeefn).toAffine();
  const parent = parseP256Descriptor(pt, 'example.com', 'https://a.example.com');
  assert.ok(eq(parent.policy!.rpIdHash, sha(Buffer.from('example.com'))));
  ok('p256 key');
  parseP256Descriptor(pt, 'a.example.com', 'https://a.example.com'); ok('p256 key');
  refused('p256 key', () => parseP256Descriptor(pt, 'a.example.org', 'https://a.example.com'), /registrable parent/, 'a mismatched RP');
  refused('p256 key', () => parseP256Descriptor(pt, 'example.com', 'https://ab.example.com'), /21-byte/, 'a 22-byte origin');
  refused('p256 key', () => parseP256Descriptor(pt, 'example12.com', 'http://example12.com'), /HTTPS/, 'http outside localhost');
  refused('p256 key', () => parseP256Descriptor({ x: 0n, y: 0n }, 'example.com', 'https://a.example.com'), /not a P-256 public key|infinity/, 'the point at infinity');
  refused('p256 key', () => checkDescriptor({ ...parent, policy: { ...parent.policy!, rpId: 'other.example' } }), /registrable parent|SHA-256 of the RP ID/, 'an RP ID that does not hash to the shown value');
}

// JubJub points.
{
  for (const k of [1n, 2n, 0xc0ffeen]) {
    const pk = upstream.compute_public_point_with_jubjub(k);
    assert.deepEqual(parseJubjubPoint(new Uint8Array([...le(pk.x, 32), ...le(pk.y, 32)])), { scheme: 'jubjub', x: pk.x, y: pk.y });
    ok('jubjub key');
  }
  const q = jubjub.Point.Fp.ORDER;
  const G = upstream.compute_public_point_with_jubjub(1n);
  refused('jubjub key', () => parseJubjubPoint({ x: 0n, y: 1n }), /small order/, 'the identity');
  refused('jubjub key', () => parseJubjubPoint({ x: 0n, y: q - 1n }), /small order/, 'the point of order 2');
  const mixed = jubjub.Point.fromAffine(G).add(jubjub.Point.fromAffine({ x: 0n, y: q - 1n })).toAffine();
  refused('jubjub key', () => parseJubjubPoint(mixed), /mixed order/, 'a mixed-order point');
  refused('jubjub key', () => parseJubjubPoint({ x: G.x + q, y: G.y }), /not canonical/, 'x not below q');
  refused('jubjub key', () => parseJubjubPoint({ x: G.x, y: G.y + 1n }), /not a JubJub point/, 'a point off the curve');
}
console.log(`  ✓ parsers: ${['evm address', 'base58', 'solana key', 'k256 key', 'p256 key', 'jubjub key'].map((k) => `${k} ${tally[k].pass}/${tally[k].refused}`).join(', ')} (accepted/refused)`);

// ── Encoders and the decoder ─────────────────────────────────────────────────

const account = rnd(32);
const sampleDescriptors = (): Descriptor[] => [
  parseJubjubPoint(upstream.compute_public_point_with_jubjub(0x1234n)),
  parseK256Descriptor(secp256k1.Point.BASE.multiply(0x5678n).toBytes(true), 0),
  parseK256Descriptor(secp256k1.Point.BASE.multiply(0x9abcn).toBytes(false), 1),
  parseP256Descriptor(p256.Point.BASE.multiply(0xdef0n).toAffine(), 'example.com', 'https://a.example.com'),
  evmDescriptor(evmAddressOf(secp256k1.Point.BASE.multiply(0x1111n).toAffine()), rnd(32)),
  solDescriptor(base58Encode(ed25519.getPublicKey(rnd(32))), rnd(32)),
];
const TAG = (r: DescriptorRecipe, d: Descriptor) => padTag(DESCRIPTOR_TAGS[r][d.scheme]);
const payloadBytes = (d: Descriptor, r: DescriptorRecipe): Uint8Array =>
  new Uint8Array(payloadParts(d, r).flatMap((p) => (p instanceof Uint8Array ? [...p] : [...le(p as bigint, 1)])));
for (let round = 0; round < 4; round++) {
  for (const d of sampleDescriptors()) {
    const epoch = BigInt(round * 7), counter = BigInt(round * 11), salt = rnd(32), oh = rnd(32), slot = BigInt(round * 60);
    const entry = derive(probe, entryCall(d, account, epoch, counter));
    const boot = derive(probe, bootCall(d, salt));
    const grant = derive(probe, grantIdCall(d, account, oh, slot));
    for (const r of ['device', 'boot', 'grant-id'] as DescriptorRecipe[]) assert.equal(payloadBytes(d, r).length, PAYLOAD_WIDTH[r][d.scheme], `${d.scheme} ${r} width`);
    // Independent SHA-256 of the preimage, every scheme.
    assert.ok(eq(entry, sha(TAG('device', d), account, payloadBytes(d, 'device'), le(epoch, 4), le(counter, 8))), `${d.scheme} entry`);
    assert.ok(eq(boot, sha(TAG('boot', d), salt, payloadBytes(d, 'boot'))), `${d.scheme} boot`);
    assert.ok(eq(grant, sha(TAG('grant-id', d), account, payloadBytes(d, 'grant-id'), oh, le(slot, 1))), `${d.scheme} grant id`);
    // Upstream's own circuits, legacy schemes.
    const A = { bytes: account };
    if (d.scheme === 'jubjub') {
      const pk = { x: d.x, y: d.y };
      assert.ok(eq(entry, upstream.derive_device_entry_with_jubjub(A, pk, epoch, counter)));
      assert.ok(eq(boot, upstream.derive_boot_commitment_with_jubjub(salt, pk)));
      assert.ok(eq(grant, upstream.derive_grant_id_with_jubjub(A, pk, oh, slot)));
    } else if (d.scheme === 'k256') {
      const pk = { x: d.x, y: d.y, identity: false };
      assert.ok(eq(entry, upstream.derive_device_entry_with_k256(A, pk, BigInt(d.envelope), epoch, counter)));
      assert.ok(eq(boot, upstream.derive_boot_commitment_with_k256(salt, pk, BigInt(d.envelope))));
      assert.ok(eq(grant, upstream.derive_grant_id_with_k256(A, pk, BigInt(d.envelope), oh, slot)));
    } else if (d.scheme === 'p256') {
      const pk = { x: d.x, y: d.y, identity: false };
      const policy = { rp_id_hash: d.policy!.rpIdHash, origin: d.policy!.origin };
      assert.ok(eq(entry, upstream.derive_device_entry_with_p256(A, pk, policy, epoch, counter)));
      assert.ok(eq(boot, upstream.derive_boot_commitment_with_p256(salt, pk, policy)));
      assert.ok(eq(grant, upstream.derive_grant_id_with_p256(A, pk, oh, slot)));
    }
    // The decoder inverts the encoder.
    for (const r of ['device', 'boot', 'grant-id'] as DescriptorRecipe[]) {
      const back = decodeDescriptor(r, TAG(r, d), payloadParts(d, r));
      assert.deepEqual(payloadParts(back, r), payloadParts(d, r), `${d.scheme} ${r} round trip`);
    }
    ok('encoders');
  }
}
{
  const [jj, , k1, , evm, sol] = sampleDescriptors();
  refused('decoder', () => decodeDescriptor('device', padTag('midnight:account:device:ed:v1'), payloadParts(sol, 'device')), /unregistered tag/, 'an unregistered tag');
  refused('decoder', () => decodeDescriptor('device', TAG('boot', sol), payloadParts(sol, 'device')), /boot tag, not a device tag/, 'another recipe\'s tag');
  refused('decoder', () => decodeDescriptor('device', TAG('device', k1), payloadParts(jj, 'device')), /takes 3 payload parts/, 'a k256 tag with a 64-byte payload');
  refused('decoder', () => decodeDescriptor('device', TAG('device', evm), payloadParts(sol, 'device')), /20 bytes/, 'an evm tag with a 32-byte identity');
  refused('decoder', () => decodeDescriptor('device', TAG('device', sol), [unhex(ED25519_TORSION_SUBGROUP[0]), rnd(32)]), /small order|canonical/, 'a Solana identity key');
  refused('decoder', () => decodeDescriptor('device', TAG('device', k1), [...payloadParts(k1, 'device').slice(0, 2), 2n]), /unknown k256 envelope/, 'envelope 2');
  refused('decoder', () => decodeDescriptor('device', TAG('device', evm), [new Uint8Array(20), rnd(32)]), /zero address/, 'the zero address');
  refused('decoder', () => decodeDescriptor('device', TAG('device', jj), [le(0n, 32), le(1n, 32)]), /small order/, 'the JubJub identity');
}
console.log(`  ✓ encoders: ${tally.encoders.pass} descriptors × 3 recipes equal SHA-256 of the preimage and upstream's circuits; decoder round trips; ${tally.decoder.refused} malformed calls refused`);

// ── Display ──────────────────────────────────────────────────────────────────

{
  const [, , , pk, evm, sol] = sampleDescriptors();
  const lines = (r: DescriptorRecipe, d: Descriptor) => Object.fromEntries(describeDescriptor(r, d).map((l) => [l.label, l.value]));
  const e = lines('device', evm);
  assert.equal(e['Ethereum address'], evmChecksumAddress((evm as any).address));
  assert.equal(e['Device privacy salt'], '0x' + hex((evm as any).blind));
  assert.equal(lines('device', sol)['Solana public key'], base58Encode((sol as any).key));
  const p = lines('device', pk);
  assert.equal(p['Passkey origin'], 'https://a.example.com');
  assert.match(p['Passkey RP (hash)'], /^0x[0-9a-f]{64} \(RP ID example\.com, shown by this client\)$/);
  assert.equal(lines('grant-id', pk)['Passkey origin'], undefined, 'a p256 grant id binds the key only');
  assert.equal(lines('device', pk)['Scheme tag'], 'midnight:account:device:r1:v2');
  console.log('  ✓ display: EIP-55 address, base58 key, passkey origin as text, the two labelled values');
}

// ── Grant origin labels ──────────────────────────────────────────────────────

for (const s of ['Midnight Night Market', 'wallet.example', 'MN Bank - grants v1']) {
  const l = grantLabel(s);
  assert.equal(ascii(probe.label_text_32(l)).trimEnd(), s);
  assert.ok(eq(grantOriginHash(l), probe.derive_grant_origin_hash_label(l)));
  ok('labels');
}
assert.ok(eq(grantOriginHash(new Uint8Array(Buffer.from('https://a.example.com'))), probe.derive_grant_origin_hash_origin(new Uint8Array(Buffer.from('https://a.example.com')))));
for (const [why, s] of [['a leading space', ' a'], ['a trailing space', 'a '], ['a double space', 'a  b'], ['empty', ''], ['33 bytes', 'x'.repeat(33)], ['a newline', 'a\nb']]) {
  refused('labels', () => grantLabel(s), /label is/, why);
}

// ── Blind: request message ───────────────────────────────────────────────────

const evmWallet = evmAddressOf(secp256k1.Point.BASE.toAffine()); // 0x7E5F…5Bdf, the key 1
const solWallet = unhex(RFC8032_PK);
const GOLDEN_EVM = [
  'Midnight Passport account privacy key (v1)',
  'Network: undeployed',
  'Wallet: Ethereum address 0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf',
  'Account index: 0',
  'Warning: this signature reveals the privacy key of this Passport account.',
  'Anyone who obtains it can link this wallet to that account.',
  'Sign it only in a Midnight Passport client you trust.',
  'It authorises nothing: no transfer, no new device, no grant.',
].join('\n');
assert.equal(blindMessage({ scheme: 'evm_eip712', network: 'undeployed', identity: evmWallet, accountIndex: 0 }), GOLDEN_EVM);
const solMsg = blindMessage({ scheme: 'sol_ed25519', network: 'preprod', identity: solWallet, accountIndex: 7n });
assert.equal(solMsg.split('\n')[2], `Wallet: Solana public key ${base58Encode(solWallet)}`);
assert.equal(solMsg.split('\n')[3], 'Account index: 7');
assert.ok(/^[\x20-\x7e\n]+$/.test(solMsg) && !solMsg.endsWith('\n'), 'printable ASCII, LF lines, no trailing newline');
assert.ok(eq(blindMessageBytes({ scheme: 'sol_ed25519', network: 'preprod', identity: solWallet, accountIndex: 7 }), new TextEncoder().encode(solMsg)), 'deterministic');
assert.notEqual(blindMessage({ scheme: 'evm_eip712', network: 'preview', identity: evmWallet, accountIndex: 0 }), GOLDEN_EVM, 'the network changes the message');
assert.notEqual(blindMessage({ scheme: 'evm_eip712', network: 'undeployed', identity: evmWallet, accountIndex: 1 }), GOLDEN_EVM, 'the account index changes the message');
const req = { scheme: 'evm_eip712' as const, network: 'undeployed', identity: evmWallet, accountIndex: 0 };
refused('blind message', () => blindMessage({ ...req, network: 'Mainnet' }), /network name/, 'an upper-case network');
refused('blind message', () => blindMessage({ ...req, network: 'pre prod' }), /network name/, 'a space in the network');
refused('blind message', () => blindMessage({ ...req, network: '' }), /network name/, 'an empty network');
refused('blind message', () => blindMessage({ ...req, accountIndex: -1 }), /0 to 4294967295/, 'a negative index');
refused('blind message', () => blindMessage({ ...req, accountIndex: 2n ** 32n }), /0 to 4294967295/, 'an index above 2^32 - 1');
refused('blind message', () => blindMessage({ ...req, accountIndex: 1.5 }), /integer/, 'a fractional index');
refused('blind message', () => blindMessage({ ...req, identity: new Uint8Array(20) }), /not zero/, 'the zero address');
refused('blind message', () => blindMessage({ ...req, identity: rnd(21) }), /20 bytes/, 'a 21-byte address');
refused('blind message', () => blindMessage({ scheme: 'sol_ed25519', network: 'preprod', identity: unhex(ED25519_TORSION_SUBGROUP[0]), accountIndex: 0 }), /small order|canonical/, 'a Solana identity key');
console.log(`  ✓ blind message: golden EVM text, Solana text, deterministic; ${tally['blind message'].refused} bad requests refused`);

// ── Blind: canonical signatures and the sign-twice check ─────────────────────

const N = secp256k1.Point.Fn.ORDER;
const be = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
// EIP-191 personal_sign over the request message, as MetaMask returns it: r || s || v.
const personalSign = (sk: Uint8Array, msg: Uint8Array, hedged = false): Uint8Array => {
  const digest = keccak_256(new Uint8Array([...new TextEncoder().encode(`\x19Ethereum Signed Message:\n${msg.length}`), ...msg]));
  const rec = secp256k1.sign(digest, sk, { prehash: false, format: 'recovered', ...(hedged ? { extraEntropy: true } : {}) });
  // noble's recovered format: recovery byte, then r || s.
  return new Uint8Array([...rec.subarray(1), 27 + rec[0]]);
};
{
  const sk = be(1n);
  const msg = blindMessageBytes(req);
  const a = personalSign(sk, msg), b = personalSign(sk, msg);
  assert.ok(sameCanonicalSignature('evm_eip712', a, b), 'RFC 6979: signing twice gives one canonical form');
  const c = canonicalEvmSignature(a);
  const r = BigInt('0x' + hex(c.subarray(0, 32))), s = BigInt('0x' + hex(c.subarray(32)));
  assert.ok(s <= N / 2n, 'low S');
  const highS = new Uint8Array([...be(r), ...be(N - s), a[64] === 27 ? 28 : 27]); // the twin recovers with the other parity
  assert.ok(eq(canonicalEvmSignature(highS), c), 'the high-S twin has the same canonical form');
  assert.ok(eq(canonicalEvmSignature(a.subarray(0, 64)), c), '64-byte form');
  const hedged1 = personalSign(sk, msg, true), hedged2 = personalSign(sk, msg, true);
  assert.equal(sameCanonicalSignature('evm_eip712', hedged1, hedged2), false, 'a hedged signer fails the sign-twice check');
  refused('evm canonical', () => canonicalEvmSignature(new Uint8Array([...be(0n), ...be(s), 27])), /outside \[1, n\)/, 'r = 0');
  refused('evm canonical', () => canonicalEvmSignature(new Uint8Array([...be(r), ...be(0n), 27])), /outside \[1, n\)/, 's = 0');
  refused('evm canonical', () => canonicalEvmSignature(new Uint8Array([...be(r), ...be(N), 27])), /outside \[1, n\)/, 's = n');
  refused('evm canonical', () => canonicalEvmSignature(new Uint8Array([...be(N + 1n), ...be(s), 27])), /outside \[1, n\)/, 'r above n');
  refused('evm canonical', () => canonicalEvmSignature(new Uint8Array([...c, 29])), /recovery byte/, 'v = 29');
  refused('evm canonical', () => canonicalEvmSignature(c.subarray(0, 63)), /64 or 65 bytes/, '63 bytes');
  const blind = deriveBlind('evm_eip712', c);
  assert.ok(eq(blind, probe.derive_blind(padTag(BLIND_TAGS.evm_eip712), c)), 'derive_blind (circuit) == deriveBlind (client)');
  assert.ok(eq(blind, derive(probe, blindCall('evm_eip712', c))));
  assert.ok(eq(blind, sha(padTag('midnight:account:blind:evm:v2'), c)));
  console.log(`  ✓ EVM canonical form: low-S r || s; high-S twin and 64/65-byte forms agree; hedged signer refused by the sign-twice check; ${tally['evm canonical'].refused} malformed signatures refused`);
}
{
  const seed = rnd(32);
  const pk = ed25519.getPublicKey(seed);
  const msg = blindMessageBytes({ scheme: 'sol_ed25519', network: 'undeployed', identity: pk, accountIndex: 0 });
  const a = ed25519.sign(msg, seed), b = ed25519.sign(msg, seed);
  assert.ok(ed25519.verify(a, msg, pk, { zip215: false }));
  assert.ok(sameCanonicalSignature('sol_ed25519', a, b), 'RFC 8032: signing twice gives one canonical form');
  const L = ed25519.Point.Fn.ORDER;
  const sPlusL = new Uint8Array([...a.subarray(0, 32), ...le(bigLE(a.subarray(32)) + L, 32)]);
  refused('ed25519 canonical', () => canonicalEd25519Signature(sPlusL), /not below the group order/, 'S + L');
  const badR = new Uint8Array(a); badR.set(le(ed25519.Point.Fp.ORDER + 1n, 32), 0);
  refused('ed25519 canonical', () => canonicalEd25519Signature(badR), /canonical point encoding/, 'a non-canonical R');
  refused('ed25519 canonical', () => canonicalEd25519Signature(a.subarray(0, 63)), /64 bytes/, '63 bytes');
  const c = canonicalEd25519Signature(a);
  assert.ok(eq(deriveBlind('sol_ed25519', c), probe.derive_blind(padTag(BLIND_TAGS.sol_ed25519), c)));
  assert.ok(eq(deriveBlind('sol_ed25519', c), sha(padTag('midnight:account:blind:sol:v1'), c)));
  assert.ok(!eq(deriveBlind('sol_ed25519', c), deriveBlind('evm_eip712', c)), 'the blind tags separate the schemes');
  console.log(`  ✓ Ed25519 canonical form: raw R || S; deterministic; ${tally['ed25519 canonical'].refused} malformed signatures refused`);
}

const report = { suite: 'wallet-arms-client-offline', seed: SEED, ranAt: new Date().toISOString(), tally, goldenEvmMessage: GOLDEN_EVM, solanaMessage: solMsg, verdict: 'PASS' };
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'wallet-arms-client-offline.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log('\n◆ wallet-arms-client-offline: PASS');
