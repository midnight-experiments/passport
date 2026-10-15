// Offline suite for the readable-descriptor module (contracts/modules/
// WalletArmDescriptors.compact), compiled through the base probe contract.
//
//   1. Tags: every registered tag fits its 32-byte pad, is ASCII, and is
//      registered once.
//   2. Legacy recipes: for `jubjub`, `k256` and `p256`, the descriptor
//      derivation by payload width equals upstream's own derivation circuit
//      (device entry, boot commitment, and grant id) AND an independent SHA-256
//      of the plain concatenation, on seeded vectors with the edge values
//      of the recipe premise check (fixed-width little-endian integers,
//      little-endian coordinates, passkeys whose RP ID is a registrable
//      parent of the origin host).
//   3. New recipes (`evm_eip712`, `sol_ed25519`): device entry, boot
//      commitment, grant id, the grantee origin label, and the blind equal an
//      independent SHA-256 of their specified preimages.
//   4. Refusals: an unknown tag, a known tag of another width or another
//      recipe, and a non-canonically padded tag are each refused by every
//      derivation; a mismatched passkey RP yields an entry the passkey
//      cannot use.
//   5. Comparator controls: the independent implementation detects a
//      one-byte change, so agreement is not vacuous.
//
// Needs the compiled probe (npm run compile). Writes
// $EVIDENCE_DIR/wallet-arms-descriptors-offline.json when EVIDENCE_DIR is
// set; never writes into the repository.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { pureCircuits as probe } from '../../contracts/managed/probe-wallet-arms-base/contract/index.js';
import { pureCircuits as upstream } from '../wallet/contract.js';

const VECTORS = 24;

// ── Independent encoders (no contract code) ─────────────────────────────────

const sha = (...parts: Uint8Array[]): Uint8Array => {
  const h = createHash('sha256');
  for (const p of parts) h.update(p);
  return new Uint8Array(h.digest());
};
const pad = (w: number, s: string): Uint8Array => {
  const b = Buffer.from(s, 'ascii');
  if (b.length > w) throw new Error(`tag exceeds ${w} bytes: ${s}`);
  const o = new Uint8Array(w);
  o.set(b);
  return o;
};
const le = (v: bigint, w: number): Uint8Array => {
  const o = new Uint8Array(w);
  let x = v;
  for (let i = 0; i < w; i++) { o[i] = Number(x & 0xffn); x >>= 8n; }
  if (x !== 0n) throw new Error(`value exceeds ${w} bytes`);
  return o;
};
const hex = (b: Uint8Array): string => Buffer.from(b).toString('hex');
const eq = (a: Uint8Array, b: Uint8Array): boolean => Buffer.from(a).equals(Buffer.from(b));
const bigLE = (b: Uint8Array): bigint => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };

// Seeded byte stream (SHA-256 in counter mode), so every run checks the same
// vectors and a failure is reproducible.
let streamCounter = 0n;
const SEED = 'aa00067/s1/wallet-arms-descriptors-offline/v1';
const rnd = (n: number): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) {
    out.set(sha(Buffer.from(SEED), le(streamCounter++, 8)).subarray(0, Math.min(32, n - i)), i);
  }
  return out;
};

// ── Inputs: the recipe premise check's edge values, then seeded values ─────

const U32_EDGES = [0n, 1n, 255n, 256n, 65535n, 65536n, 0x7fffffffn, 0xffffffffn];
const U64_EDGES = [0n, 1n, 255n, 256n, 0xffffffffn, 0x100000000n, 0x7fffffffffffffffn, 0xffffffffffffffffn];
const SLOT_EDGES = [0n, 255n];
const SECP256K1_N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
const SECP256R1_N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n;
const JUBJUB_R = 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7n;
const pick = (edges: bigint[], i: number, bytes: number): bigint => (i < edges.length ? edges[i] : bigLE(rnd(bytes)));
const scalar = (n: bigint, i: number, edges: bigint[]): bigint => (i < edges.length ? edges[i] : (bigLE(rnd(40)) % (n - 1n)) + 1n);
const jubjubPk = (i: number) => upstream.compute_public_point_with_jubjub(scalar(JUBJUB_R, i, [1n, 2n, 5n, JUBJUB_R - 1n]));
const k256Pk = (i: number) => upstream.compute_public_point_with_k256(scalar(SECP256K1_N, i, [1n, 2n, SECP256K1_N - 1n]));
const p256Pk = (i: number) => upstream.compute_public_point_with_p256(scalar(SECP256R1_N, i, [1n, 2n, SECP256R1_N - 1n]));
const xy = (p: { x: bigint; y: bigint }): [Uint8Array, Uint8Array] => [le(p.x, 32), le(p.y, 32)];

// 21-byte origins: an RP ID that is a registrable PARENT of the origin host,
// one equal to the host, and http://localhost.
const ORIGINS = [
  { origin: 'https://a.example.com', rpId: 'example.com', note: 'RP ID is a registrable parent of the origin host' },
  { origin: 'https://a.example.com', rpId: 'a.example.com', note: 'RP ID equals the origin host' },
  { origin: 'https://bank.example1', rpId: 'bank.example1', note: 'RP ID equals the origin host' },
  { origin: 'https://x.y.bank.test', rpId: 'bank.test', note: 'RP ID is a registrable parent, two labels up' },
  { origin: 'http://localhost:5173', rpId: 'localhost', note: 'http://localhost origin' },
];
const policyOf = (i: number) => {
  if (i < ORIGINS.length) {
    const o = ORIGINS[i];
    return { rp_id_hash: sha(Buffer.from(o.rpId, 'ascii')), origin: new Uint8Array(Buffer.from(o.origin, 'ascii')), note: o.note };
  }
  return { rp_id_hash: rnd(32), origin: rnd(21), note: 'random policy bytes' };
};
const addr = () => rnd(32);
const contractAddress = (b: Uint8Array) => ({ bytes: b });

// ── Report ──────────────────────────────────────────────────────────────────

interface RecipeResult { vectors: number; agree: number; first: unknown[] }
const report: {
  suite: string; seed: string; ranAt: string; tags: unknown[];
  legacy: Record<string, RecipeResult>; fresh: Record<string, RecipeResult>;
  refusals: Record<string, { cases: number; refused: number }>;
  controls: Record<string, boolean>; verdict: string;
} = {
  suite: 'wallet-arms-descriptors-offline', seed: SEED, ranAt: new Date().toISOString(),
  tags: [], legacy: {}, fresh: {}, refusals: {}, controls: {}, verdict: 'FAIL',
};

function recipe(
  table: Record<string, RecipeResult>, name: string,
  run: (i: number) => { values: Uint8Array[]; vector: Record<string, unknown> },
): void {
  const r: RecipeResult = { vectors: VECTORS, agree: 0, first: [] };
  for (let i = 0; i < VECTORS; i++) {
    const { values, vector } = run(i);
    const all = values.every((v) => eq(v, values[0]));
    assert.ok(all, `${name} #${i}: ${values.map(hex).join(' / ')}`);
    r.agree++;
    if (r.first.length < 3) r.first.push({ i, ...vector, result: hex(values[0]) });
  }
  table[name] = r;
  console.log(`  ✓ ${name}: ${r.agree}/${VECTORS}`);
}

// ── 1. Tags ─────────────────────────────────────────────────────────────────

console.log('\n── tags');
const TAGS: [string, () => Uint8Array, string][] = [
  ['device', probe.device_tag_jubjub, 'midnight:account:device:v1'],
  ['device', probe.device_tag_k256, 'midnight:account:device:k1:v2'],
  ['device', probe.device_tag_p256, 'midnight:account:device:r1:v2'],
  ['device', probe.device_tag_evm_eip712, 'midnight:account:device:evm:v2'],
  ['device', probe.device_tag_sol_ed25519, 'midnight:account:device:sol:v1'],
  ['boot', probe.boot_tag_jubjub, 'midnight:account:boot:v1'],
  ['boot', probe.boot_tag_k256, 'midnight:account:boot:k1:v2'],
  ['boot', probe.boot_tag_p256, 'midnight:account:boot:r1:v2'],
  ['boot', probe.boot_tag_evm_eip712, 'midnight:account:boot:evm:v2'],
  ['boot', probe.boot_tag_sol_ed25519, 'midnight:account:boot:sol:v1'],
  ['grant-id', probe.grant_id_tag_jubjub, 'midnight:account:grant:id:v1'],
  ['grant-id', probe.grant_id_tag_k256, 'midnight:account:grant:id:k1:v1'],
  ['grant-id', probe.grant_id_tag_p256, 'midnight:account:grant:id:r1:v1'],
  ['grant-id', probe.grant_id_tag_evm_eip712, 'midnight:account:grant:id:evm:v2'],
  ['grant-id', probe.grant_id_tag_sol_ed25519, 'midnight:account:grant:id:sol:v1'],
  ['blind', probe.blind_tag_evm_eip712, 'midnight:account:blind:evm:v2'],
  ['blind', probe.blind_tag_sol_ed25519, 'midnight:account:blind:sol:v1'],
  ['grant-origin', probe.grant_origin_tag, 'midnight:account:grant:origin:v1'],
];
const seen = new Set<string>();
for (const [kind, f, text] of TAGS) {
  const t = f();
  assert.equal(t.length, 32, `${text}: pad width`);
  assert.ok(/^[\x21-\x7e]+$/.test(text), `${text}: visible ASCII`);
  assert.ok(text.length <= 32, `${text}: ${text.length} > 32 bytes`);
  assert.ok(eq(t, pad(32, text)), `${text}: circuit constant differs from pad(32, text)`);
  assert.ok(!seen.has(text), `${text}: registered twice`);
  seen.add(text);
  report.tags.push({ kind, text, bytes: text.length, pad: 32, margin: 32 - text.length });
}
// The new arms' tags: markers `evm` (from v2) and `sol` (from v1).
for (const text of seen) {
  if (/:evm:/.test(text)) assert.ok(text.endsWith(':v2'), `${text}: evm tags start at v2`);
  if (/:sol:/.test(text)) assert.ok(text.endsWith(':v1'), `${text}: sol tags start at v1`);
}
console.log(`  ✓ ${TAGS.length} tags fit 32 bytes, distinct, ASCII (widest: ${Math.max(...[...seen].map((s) => s.length))} bytes)`);

// ── 2. Legacy recipes: descriptor == upstream circuit == independent SHA-256

console.log('\n── legacy recipes (descriptor by width == upstream circuit == SHA-256)');
const T = (s: string) => pad(32, s);

recipe(report.legacy, 'device entry jubjub (w64)', (i) => {
  const a = addr(), pk = jubjubPk(i), [x, y] = xy(pk), ep = pick(U32_EDGES, i, 4), ct = pick(U64_EDGES, i, 8);
  return {
    values: [
      probe.derive_descriptor_entry_w64(T('midnight:account:device:v1'), contractAddress(a), x, y, ep, ct),
      upstream.derive_device_entry_with_jubjub(contractAddress(a), pk, ep, ct),
      sha(T('midnight:account:device:v1'), a, x, y, le(ep, 4), le(ct, 8)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), epoch: ep, counter: ct },
  };
});
recipe(report.legacy, 'device entry k256 (w65)', (i) => {
  const a = addr(), pk = k256Pk(i), [x, y] = xy(pk), env = BigInt(i % 2), ep = pick(U32_EDGES, i, 4), ct = pick(U64_EDGES, i, 8);
  return {
    values: [
      probe.derive_descriptor_entry_w65(T('midnight:account:device:k1:v2'), contractAddress(a), x, y, env, ep, ct),
      upstream.derive_device_entry_with_k256(contractAddress(a), pk, env, ep, ct),
      sha(T('midnight:account:device:k1:v2'), a, x, y, le(env, 1), le(ep, 4), le(ct, 8)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), envelope: env, epoch: ep, counter: ct },
  };
});
recipe(report.legacy, 'device entry p256 (w117)', (i) => {
  const a = addr(), pk = p256Pk(i), [x, y] = xy(pk), p = policyOf(i), ep = pick(U32_EDGES, i, 4), ct = pick(U64_EDGES, i, 8);
  return {
    values: [
      probe.derive_descriptor_entry_w117(T('midnight:account:device:r1:v2'), contractAddress(a), x, y, p.rp_id_hash, p.origin, ep, ct),
      upstream.derive_device_entry_with_p256(contractAddress(a), pk, { rp_id_hash: p.rp_id_hash, origin: p.origin }, ep, ct),
      sha(T('midnight:account:device:r1:v2'), a, x, y, p.rp_id_hash, p.origin, le(ep, 4), le(ct, 8)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), rp_id_hash: hex(p.rp_id_hash), origin: hex(p.origin), note: p.note, epoch: ep, counter: ct },
  };
});
recipe(report.legacy, 'boot jubjub (w64)', (i) => {
  const s = rnd(32), pk = jubjubPk(i), [x, y] = xy(pk);
  return {
    values: [
      probe.derive_descriptor_boot_w64(T('midnight:account:boot:v1'), s, x, y),
      upstream.derive_boot_commitment_with_jubjub(s, pk),
      sha(T('midnight:account:boot:v1'), s, x, y),
    ],
    vector: { salt: hex(s), x: hex(x), y: hex(y) },
  };
});
recipe(report.legacy, 'boot k256 (w65)', (i) => {
  const s = rnd(32), pk = k256Pk(i), [x, y] = xy(pk), env = BigInt(i % 2);
  return {
    values: [
      probe.derive_descriptor_boot_w65(T('midnight:account:boot:k1:v2'), s, x, y, env),
      upstream.derive_boot_commitment_with_k256(s, pk, env),
      sha(T('midnight:account:boot:k1:v2'), s, x, y, le(env, 1)),
    ],
    vector: { salt: hex(s), x: hex(x), y: hex(y), envelope: env },
  };
});
recipe(report.legacy, 'boot p256 (w117)', (i) => {
  const s = rnd(32), pk = p256Pk(i), [x, y] = xy(pk), p = policyOf(i);
  return {
    values: [
      probe.derive_descriptor_boot_w117(T('midnight:account:boot:r1:v2'), s, x, y, p.rp_id_hash, p.origin),
      upstream.derive_boot_commitment_with_p256(s, pk, { rp_id_hash: p.rp_id_hash, origin: p.origin }),
      sha(T('midnight:account:boot:r1:v2'), s, x, y, p.rp_id_hash, p.origin),
    ],
    vector: { salt: hex(s), x: hex(x), y: hex(y), rp_id_hash: hex(p.rp_id_hash), origin: hex(p.origin), note: p.note },
  };
});
recipe(report.legacy, 'grant id jubjub (w64)', (i) => {
  const a = addr(), pk = jubjubPk(i), [x, y] = xy(pk), oh = rnd(32), slot = pick(SLOT_EDGES, i, 1);
  return {
    values: [
      probe.derive_descriptor_grant_id_w64(T('midnight:account:grant:id:v1'), contractAddress(a), x, y, oh, slot),
      upstream.derive_grant_id_with_jubjub(contractAddress(a), pk, oh, slot),
      sha(T('midnight:account:grant:id:v1'), a, x, y, oh, le(slot, 1)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), origin_hash: hex(oh), slot },
  };
});
recipe(report.legacy, 'grant id k256 (w65)', (i) => {
  const a = addr(), pk = k256Pk(i), [x, y] = xy(pk), env = BigInt(i % 2), oh = rnd(32), slot = pick(SLOT_EDGES, i, 1);
  return {
    values: [
      probe.derive_descriptor_grant_id_w65(T('midnight:account:grant:id:k1:v1'), contractAddress(a), x, y, env, oh, slot),
      upstream.derive_grant_id_with_k256(contractAddress(a), pk, env, oh, slot),
      sha(T('midnight:account:grant:id:k1:v1'), a, x, y, le(env, 1), oh, le(slot, 1)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), envelope: env, origin_hash: hex(oh), slot },
  };
});
recipe(report.legacy, 'grant id p256 (w64)', (i) => {
  const a = addr(), pk = p256Pk(i), [x, y] = xy(pk), oh = rnd(32), slot = pick(SLOT_EDGES, i, 1);
  return {
    values: [
      probe.derive_descriptor_grant_id_w64(T('midnight:account:grant:id:r1:v1'), contractAddress(a), x, y, oh, slot),
      upstream.derive_grant_id_with_p256(contractAddress(a), pk, oh, slot),
      sha(T('midnight:account:grant:id:r1:v1'), a, x, y, oh, le(slot, 1)),
    ],
    vector: { self: hex(a), x: hex(x), y: hex(y), origin_hash: hex(oh), slot },
  };
});
// A passkey grantee's origin_hash: the probe recipe, upstream's client
// originHash() over the same 21 bytes, and SHA-256 (authenticate_grant_with_p256
// recomputes the same expression in-circuit; the recipe premise check
// compared it with a probe copy of that expression).
const { originHash } = await import('../wallet/signer.js');
recipe(report.legacy, 'grant origin_hash of a 21-byte passkey origin', (i) => {
  const o = i < ORIGINS.length ? new Uint8Array(Buffer.from(ORIGINS[i].origin, 'ascii')) : rnd(21).map((b) => 0x21 + (b % 94));
  return {
    values: [
      probe.derive_grant_origin_hash_origin(o),
      originHash(Buffer.from(o).toString('ascii')),
      sha(T('midnight:account:grant:origin:v1'), o),
    ],
    vector: { origin: Buffer.from(o).toString('ascii') },
  };
});

// ── 3. New recipes: descriptor == independent SHA-256 of the spec preimage ──

console.log('\n── new recipes (descriptor == SHA-256 of the specified preimage)');
recipe(report.fresh, 'device entry evm_eip712 (w52)', (i) => {
  const a = addr(), address = rnd(20), blind = rnd(32), ep = pick(U32_EDGES, i, 4), ct = pick(U64_EDGES, i, 8);
  return {
    values: [
      probe.derive_descriptor_entry_w52(T('midnight:account:device:evm:v2'), contractAddress(a), address, blind, ep, ct),
      sha(T('midnight:account:device:evm:v2'), a, address, blind, le(ep, 4), le(ct, 8)),
    ],
    vector: { self: hex(a), address: hex(address), blind: hex(blind), epoch: ep, counter: ct },
  };
});
recipe(report.fresh, 'device entry sol_ed25519 (w64)', (i) => {
  const a = addr(), key = rnd(32), blind = rnd(32), ep = pick(U32_EDGES, i, 4), ct = pick(U64_EDGES, i, 8);
  return {
    values: [
      probe.derive_descriptor_entry_w64(T('midnight:account:device:sol:v1'), contractAddress(a), key, blind, ep, ct),
      sha(T('midnight:account:device:sol:v1'), a, key, blind, le(ep, 4), le(ct, 8)),
    ],
    vector: { self: hex(a), key: hex(key), blind: hex(blind), epoch: ep, counter: ct },
  };
});
recipe(report.fresh, 'boot evm_eip712 (w52)', () => {
  const s = rnd(32), address = rnd(20), blind = rnd(32);
  return {
    values: [
      probe.derive_descriptor_boot_w52(T('midnight:account:boot:evm:v2'), s, address, blind),
      sha(T('midnight:account:boot:evm:v2'), s, address, blind),
    ],
    vector: { salt: hex(s), address: hex(address), blind: hex(blind) },
  };
});
recipe(report.fresh, 'boot sol_ed25519 (w64)', () => {
  const s = rnd(32), key = rnd(32), blind = rnd(32);
  return {
    values: [
      probe.derive_descriptor_boot_w64(T('midnight:account:boot:sol:v1'), s, key, blind),
      sha(T('midnight:account:boot:sol:v1'), s, key, blind),
    ],
    vector: { salt: hex(s), key: hex(key), blind: hex(blind) },
  };
});
recipe(report.fresh, 'grant id evm_eip712 (w52)', (i) => {
  const a = addr(), address = rnd(20), blind = rnd(32), oh = rnd(32), slot = pick(SLOT_EDGES, i, 1);
  return {
    values: [
      probe.derive_descriptor_grant_id_w52(T('midnight:account:grant:id:evm:v2'), contractAddress(a), address, blind, oh, slot),
      sha(T('midnight:account:grant:id:evm:v2'), a, address, blind, oh, le(slot, 1)),
    ],
    vector: { self: hex(a), address: hex(address), blind: hex(blind), origin_hash: hex(oh), slot },
  };
});
recipe(report.fresh, 'grant id sol_ed25519 (w64)', (i) => {
  const a = addr(), key = rnd(32), blind = rnd(32), oh = rnd(32), slot = pick(SLOT_EDGES, i, 1);
  return {
    values: [
      probe.derive_descriptor_grant_id_w64(T('midnight:account:grant:id:sol:v1'), contractAddress(a), key, blind, oh, slot),
      sha(T('midnight:account:grant:id:sol:v1'), a, key, blind, oh, le(slot, 1)),
    ],
    vector: { self: hex(a), key: hex(key), blind: hex(blind), origin_hash: hex(oh), slot },
  };
});
const LABELS = ['Midnight Night Market', 'wallet.example', 'a', 'x'.repeat(32), 'MN Bank - grants v1'];
recipe(report.fresh, 'grant origin_hash of a 32-byte label', (i) => {
  const label = i < LABELS.length ? pad(32, LABELS[i]) : rnd(32);
  return {
    values: [probe.derive_grant_origin_hash_label(label), sha(T('midnight:account:grant:origin:v1'), label)],
    vector: { label: hex(label) },
  };
});
recipe(report.fresh, 'blind evm_eip712', () => {
  const sig = rnd(64);
  return { values: [probe.derive_blind(T('midnight:account:blind:evm:v2'), sig), sha(T('midnight:account:blind:evm:v2'), sig)], vector: { signature: hex(sig) } };
});
recipe(report.fresh, 'blind sol_ed25519', () => {
  const sig = rnd(64);
  return { values: [probe.derive_blind(T('midnight:account:blind:sol:v1'), sig), sha(T('midnight:account:blind:sol:v1'), sig)], vector: { signature: hex(sig) } };
});

// ── 4. Refusals ─────────────────────────────────────────────────────────────

console.log('\n── refusals (tags are not free-form)');
const A = contractAddress(rnd(32)), B32 = rnd(32), B20 = rnd(20), B21 = rnd(21);
const derivations: Record<string, { allowed: string[]; run: (tag: Uint8Array) => unknown }> = {
  entry_w52: { allowed: ['midnight:account:device:evm:v2'], run: (t) => probe.derive_descriptor_entry_w52(t, A, B20, B32, 0n, 0n) },
  entry_w64: { allowed: ['midnight:account:device:v1', 'midnight:account:device:sol:v1'], run: (t) => probe.derive_descriptor_entry_w64(t, A, B32, B32, 0n, 0n) },
  entry_w65: { allowed: ['midnight:account:device:k1:v2'], run: (t) => probe.derive_descriptor_entry_w65(t, A, B32, B32, 0n, 0n, 0n) },
  entry_w117: { allowed: ['midnight:account:device:r1:v2'], run: (t) => probe.derive_descriptor_entry_w117(t, A, B32, B32, B32, B21, 0n, 0n) },
  boot_w52: { allowed: ['midnight:account:boot:evm:v2'], run: (t) => probe.derive_descriptor_boot_w52(t, B32, B20, B32) },
  boot_w64: { allowed: ['midnight:account:boot:v1', 'midnight:account:boot:sol:v1'], run: (t) => probe.derive_descriptor_boot_w64(t, B32, B32, B32) },
  boot_w65: { allowed: ['midnight:account:boot:k1:v2'], run: (t) => probe.derive_descriptor_boot_w65(t, B32, B32, B32, 0n) },
  boot_w117: { allowed: ['midnight:account:boot:r1:v2'], run: (t) => probe.derive_descriptor_boot_w117(t, B32, B32, B32, B32, B21) },
  grant_id_w52: { allowed: ['midnight:account:grant:id:evm:v2'], run: (t) => probe.derive_descriptor_grant_id_w52(t, A, B20, B32, B32, 0n) },
  grant_id_w64: { allowed: ['midnight:account:grant:id:v1', 'midnight:account:grant:id:r1:v1', 'midnight:account:grant:id:sol:v1'], run: (t) => probe.derive_descriptor_grant_id_w64(t, A, B32, B32, B32, 0n) },
  grant_id_w65: { allowed: ['midnight:account:grant:id:k1:v1'], run: (t) => probe.derive_descriptor_grant_id_w65(t, A, B32, B32, 0n, B32, 0n) },
  blind: { allowed: ['midnight:account:blind:evm:v2', 'midnight:account:blind:sol:v1'], run: (t) => probe.derive_blind(t, rnd(64)) },
};
// Candidate tags: every registered tag, plus unknown, unregistered-version,
// space-padded, upper-case and all-zero tags.
const spacePadded = (s: string) => { const o = new Uint8Array(32).fill(0x20); o.set(Buffer.from(s, 'ascii')); return o; };
const candidates: [string, Uint8Array][] = [
  ...[...seen].map((s) => [s, pad(32, s)] as [string, Uint8Array]),
  ['(unknown) midnight:account:device:ed:v1', pad(32, 'midnight:account:device:ed:v1')],
  ['(unknown) midnight:account:device:evm:v1', pad(32, 'midnight:account:device:evm:v1')],
  ['(unknown) midnight:account:device:sol:v2', pad(32, 'midnight:account:device:sol:v2')],
  ['(unknown) MIDNIGHT:ACCOUNT:DEVICE:V1', pad(32, 'MIDNIGHT:ACCOUNT:DEVICE:V1')],
  ['(non-canonical padding) midnight:account:device:v1 + spaces', spacePadded('midnight:account:device:v1')],
  ['(all zero)', new Uint8Array(32)],
  ['(random)', rnd(32)],
];
let refusalCases = 0, refusalsSeen = 0, acceptsSeen = 0;
for (const [fname, d] of Object.entries(derivations)) {
  let cases = 0, refused = 0;
  for (const [label, tag] of candidates) {
    const allowed = d.allowed.some((s) => eq(pad(32, s), tag));
    if (allowed) {
      assert.doesNotThrow(() => d.run(tag), `${fname} must accept ${label}`);
      acceptsSeen++;
      continue;
    }
    cases++;
    assert.throws(() => d.run(tag), /failed assert: descriptor: not a/, `${fname} must refuse ${label}`);
    refused++;
  }
  report.refusals[fname] = { cases, refused };
  refusalCases += cases; refusalsSeen += refused;
}
assert.equal(acceptsSeen, Object.values(derivations).reduce((n, d) => n + d.allowed.length, 0));
console.log(`  ✓ ${refusalsSeen}/${refusalCases} wrong-tag cases refused at the generated JavaScript (each registered tag accepted only by its own recipe and width)`);

// A passkey whose descriptor carries the wrong RP (a mismatched rp_id_hash)
// derives an entry other than the one the passkey can use: the derivation
// does not "correct" the policy, and the p256 seam would refuse the passkey's
// assertions against it (authenticator data RP mismatch).
{
  const a = addr(), pk = p256Pk(10), [x, y] = xy(pk), origin = new Uint8Array(Buffer.from('https://a.example.com', 'ascii'));
  const right = sha(Buffer.from('example.com', 'ascii'));
  const wrong = sha(Buffer.from('a.example.org', 'ascii'));
  const usable = upstream.derive_device_entry_with_p256(contractAddress(a), pk, { rp_id_hash: right, origin }, 0n, 0n);
  const viaRight = probe.derive_descriptor_entry_w117(T('midnight:account:device:r1:v2'), contractAddress(a), x, y, right, origin, 0n, 0n);
  const viaWrong = probe.derive_descriptor_entry_w117(T('midnight:account:device:r1:v2'), contractAddress(a), x, y, wrong, origin, 0n, 0n);
  assert.ok(eq(viaRight, usable), 'parent-domain RP: the descriptor entry is the passkey\'s usable entry');
  assert.ok(!eq(viaWrong, usable), 'mismatched RP: the descriptor entry is not the passkey\'s usable entry');
  report.controls.parentDomainRpPositive = true;
  report.controls.mismatchedRpNegative = true;
  console.log('  ✓ parent-domain RP (example.com for https://a.example.com) derives the usable entry; a mismatched RP does not');
}

// ── 5. Comparator controls ──────────────────────────────────────────────────

{
  const a = addr(), key = rnd(32), blind = rnd(32);
  const good = probe.derive_descriptor_entry_w64(T('midnight:account:device:sol:v1'), contractAddress(a), key, blind, 3n, 9n);
  report.controls.splitDifferently = eq(good, sha(T('midnight:account:device:sol:v1'), a, Buffer.concat([key, blind]), le(3n, 4), le(9n, 8)));
  report.controls.counterOffByOne = !eq(good, sha(T('midnight:account:device:sol:v1'), a, key, blind, le(3n, 4), le(10n, 8)));
  report.controls.minimalWidthIntegers = !eq(good, sha(T('midnight:account:device:sol:v1'), a, key, blind, Buffer.from([3]), Buffer.from([9])));
  report.controls.blindOmitted = !eq(good, sha(T('midnight:account:device:sol:v1'), a, key, le(3n, 4), le(9n, 8)));
  report.controls.otherArmTag = !eq(good, sha(T('midnight:account:device:v1'), a, key, blind, le(3n, 4), le(9n, 8)));
  for (const [k, v] of Object.entries(report.controls)) assert.ok(v, `comparator control ${k}`);
  console.log(`  ✓ comparator controls: ${Object.keys(report.controls).join(', ')}`);
}

report.verdict = 'PASS';
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'wallet-arms-descriptors-offline.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, (_k, v) => (typeof v === 'bigint' ? v.toString() : v), 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log('\n◆ wallet-arms-descriptors-offline: PASS');
