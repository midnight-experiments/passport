// Readable device descriptors — client encoders and strict decoders.
//
// A readable arm (`evm_eip712`, `sol_ed25519`) shows another key as a
// DESCRIPTOR: the target recipe's tag text and the key payload in the target
// scheme's own form. The contract derives the target's device entry, boot
// commitment, or grant id from exactly those values, one circuit per payload
// class (contracts/modules/WalletArmDescriptors.compact): the byte classes
// w52, w64, w65 and w117, and the ed25519 class, which takes a Solana key as
// its Curve25519Point and derives the key's 32 bytes in-circuit. This module:
//
//   - parses the forms a person or a wallet presents (an Ethereum address, a
//     Solana public key, a SEC1 secp256k1 or P-256 key, a passkey's RP ID and
//     origin, and a JubJub point) STRICTLY, refusing anything that is not exactly
//     one canonical, admissible key;
//   - encodes a descriptor as the arguments of the class circuit that
//     derives its entry, boot commitment, or grant id (the caller runs them
//     through any `pureCircuits` object that exports the module, so the
//     derivation is always the contract's own);
//   - decodes those arguments back into a descriptor, refusing an unknown
//     tag, a tag of another width, and an inadmissible key, so a wallet can
//     check what it is asked to approve;
//   - describes a descriptor for display, with the forms a user can compare
//     by eye (EVM address, Solana key, passkey origin) and the labelled values
//     (the passkey's "Passkey RP (hash)" and a blinded key's "Device privacy
//     salt").
//
// Platform-neutral: no node:crypto, so the same code runs in Node and in a
// browser page.

import { sha256 } from '@noble/hashes/sha2.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { p256 } from '@noble/curves/nist.js';
import { ed25519 } from '@noble/curves/ed25519.js';
import { jubjub } from '@noble/curves/misc.js';
import { WEBAUTHN_ORIGIN_BYTES, webauthnPolicy } from './webauthn.js';

// ── Schemes, recipes, and tags ───────────────────────────────────────────────

export type DescriptorScheme = 'jubjub' | 'k256' | 'p256' | 'evm_eip712' | 'sol_ed25519';
export type DescriptorRecipe = 'device' | 'boot' | 'grant-id';
export const DESCRIPTOR_SCHEMES: readonly DescriptorScheme[] = ['jubjub', 'k256', 'p256', 'evm_eip712', 'sol_ed25519'];

/** The registered tag of each recipe and scheme (the module's constants). */
export const DESCRIPTOR_TAGS: Readonly<Record<DescriptorRecipe, Readonly<Record<DescriptorScheme, string>>>> = {
  device: {
    jubjub: 'midnight:account:device:v1',
    k256: 'midnight:account:device:k1:v2',
    p256: 'midnight:account:device:r1:v2',
    evm_eip712: 'midnight:account:device:evm:v1',
    sol_ed25519: 'midnight:account:device:sol:v1',
  },
  boot: {
    jubjub: 'midnight:account:boot:v1',
    k256: 'midnight:account:boot:k1:v2',
    p256: 'midnight:account:boot:r1:v2',
    evm_eip712: 'midnight:account:boot:evm:v1',
    sol_ed25519: 'midnight:account:boot:sol:v1',
  },
  'grant-id': {
    jubjub: 'midnight:account:grant:id:v1',
    k256: 'midnight:account:grant:id:k1:v1',
    p256: 'midnight:account:grant:id:r1:v1',
    evm_eip712: 'midnight:account:grant:id:evm:v1',
    sol_ed25519: 'midnight:account:grant:id:sol:v1',
  },
};

/** The blind's tag per readable scheme. */
export const BLIND_TAGS: Readonly<Record<'evm_eip712' | 'sol_ed25519', string>> = {
  evm_eip712: 'midnight:account:blind:evm:v1',
  sol_ed25519: 'midnight:account:blind:sol:v1',
};

/** Upstream's grant origin tag (scoped-grants MIP section 4.4). */
export const GRANT_ORIGIN_TAG = 'midnight:account:grant:origin:v1';

/** The width of the payload each recipe and scheme hashes (bytes). */
export const PAYLOAD_WIDTH: Readonly<Record<DescriptorRecipe, Readonly<Record<DescriptorScheme, 52 | 64 | 65 | 117>>>> = {
  device: { jubjub: 64, k256: 65, p256: 117, evm_eip712: 52, sol_ed25519: 64 },
  boot: { jubjub: 64, k256: 65, p256: 117, evm_eip712: 52, sol_ed25519: 64 },
  'grant-id': { jubjub: 64, k256: 65, p256: 64, evm_eip712: 52, sol_ed25519: 64 },
};

export type DescriptorClass = 'w52' | 'w64' | 'w65' | 'w117' | 'ed25519';

/** The circuit class of each recipe and scheme: the suffix of the module's
 *  `derive_descriptor_<recipe>_<class>` circuit. A `sol_ed25519` key has its
 *  own class (its payload is a Curve25519Point, not bytes), although the
 *  preimage it hashes is 64 bytes wide. */
export const DESCRIPTOR_CLASS: Readonly<Record<DescriptorRecipe, Readonly<Record<DescriptorScheme, DescriptorClass>>>> = {
  device: { jubjub: 'w64', k256: 'w65', p256: 'w117', evm_eip712: 'w52', sol_ed25519: 'ed25519' },
  boot: { jubjub: 'w64', k256: 'w65', p256: 'w117', evm_eip712: 'w52', sol_ed25519: 'ed25519' },
  'grant-id': { jubjub: 'w64', k256: 'w65', p256: 'w64', evm_eip712: 'w52', sol_ed25519: 'ed25519' },
};

const TEXT = new TextEncoder();
const equalBytes = (a: Uint8Array, b: Uint8Array): boolean => a.length === b.length && a.every((v, i) => v === b[i]);
const toHex = (b: Uint8Array): string => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
const fromHex = (s: string): Uint8Array => {
  if (!/^(?:[0-9a-fA-F]{2})*$/.test(s)) throw new Error('descriptor: not hexadecimal');
  return Uint8Array.from(s.match(/../g) ?? [], (h) => parseInt(h, 16));
};
const bytesLE = (v: bigint, w: number): Uint8Array => {
  const o = new Uint8Array(w);
  let x = v;
  for (let i = 0; i < w; i++) { o[i] = Number(x & 0xffn); x >>= 8n; }
  if (x !== 0n) throw new Error(`descriptor: value exceeds ${w} bytes`);
  return o;
};
const bigLE = (b: Uint8Array): bigint => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };
const bigBE = (b: Uint8Array): bigint => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const bytesBE = (v: bigint, w: number): Uint8Array => bytesLE(v, w).reverse();

/** A registered tag's 32-byte, zero-padded form. */
export function padTag(text: string): Uint8Array {
  if (!/^[\x21-\x7e]+$/.test(text)) throw new Error(`descriptor: tag is not visible ASCII: ${JSON.stringify(text)}`);
  const b = TEXT.encode(text);
  if (b.length > 32) throw new Error(`descriptor: tag exceeds 32 bytes: ${text}`);
  const out = new Uint8Array(32);
  out.set(b);
  return out;
}

/** The recipe and scheme of a registered 32-byte tag; refuses anything else,
 *  including a registered text with non-zero padding. */
export function tagOf(tag: Uint8Array): { recipe: DescriptorRecipe; scheme: DescriptorScheme; text: string } {
  if (tag.length !== 32) throw new Error('descriptor: a tag is 32 bytes');
  for (const recipe of Object.keys(DESCRIPTOR_TAGS) as DescriptorRecipe[]) {
    for (const scheme of DESCRIPTOR_SCHEMES) {
      const text = DESCRIPTOR_TAGS[recipe][scheme];
      if (equalBytes(padTag(text), tag)) return { recipe, scheme, text };
    }
  }
  throw new Error(`descriptor: unregistered tag ${toHex(tag)}`);
}

// ── Descriptors ──────────────────────────────────────────────────────────────

export interface JubjubDescriptor { scheme: 'jubjub'; x: bigint; y: bigint }
export interface K256Descriptor { scheme: 'k256'; x: bigint; y: bigint; envelope: 0 | 1 }
/** A passkey's WebAuthn policy. `rpIdHash` is a labelled value (the RP ID may
 *  be a registrable parent of the origin's host, so it cannot be derived from
 *  the origin); `rpId` is the client's own record of the RP ID, shown beside
 *  it and checked against it, never hashed by a circuit. */
export interface PasskeyPolicy { rpIdHash: Uint8Array; origin: Uint8Array; rpId?: string }
/** A passkey: its key and, for device entries and boot commitments, its
 *  policy. A grant id binds the key only (the RP is a scope field). */
export interface P256Descriptor { scheme: 'p256'; x: bigint; y: bigint; policy?: PasskeyPolicy }
export interface EvmDescriptor { scheme: 'evm_eip712'; address: Uint8Array; blind: Uint8Array }
/** A Solana key: its 32-byte RFC 8032 encoding (what the wallet exports and a
 *  person compares) and the account's blind. The circuits take the key as
 *  its point (solanaKeyPoint) and derive these 32 bytes from it. */
export interface SolDescriptor { scheme: 'sol_ed25519'; key: Uint8Array; blind: Uint8Array }
/** A Curve25519Point as the generated JavaScript takes it: affine twisted
 *  Edwards coordinates. */
export interface Curve25519Affine { x: bigint; y: bigint }
export type Descriptor = JubjubDescriptor | K256Descriptor | P256Descriptor | EvmDescriptor | SolDescriptor;

// ── Strict parsers: the forms a person or a wallet presents ─────────────────

/** EIP-55 checksummed form of a 20-byte address. */
export function evmChecksumAddress(address: Uint8Array): string {
  if (address.length !== 20) throw new Error('descriptor: an Ethereum address is 20 bytes');
  const lower = toHex(address);
  const h = toHex(keccak_256(TEXT.encode(lower)));
  let out = '0x';
  for (let i = 0; i < 40; i++) out += parseInt(h[i], 16) >= 8 ? lower[i].toUpperCase() : lower[i];
  return out;
}

/** A 0x-prefixed Ethereum address. Mixed case must carry a valid EIP-55
 *  checksum; all-lower and all-upper case carry none. The zero address is
 *  refused: no key controls it. */
export function parseEvmAddress(text: string): Uint8Array {
  if (!/^0x[0-9a-fA-F]{40}$/.test(text)) throw new Error('descriptor: an Ethereum address is 0x and 40 hex digits');
  const body = text.slice(2);
  const bytes = fromHex(body);
  const mixed = body !== body.toLowerCase() && body !== body.toUpperCase();
  if (mixed && evmChecksumAddress(bytes) !== text) throw new Error('descriptor: Ethereum address checksum mismatch');
  if (bytes.every((b) => b === 0)) throw new Error('descriptor: the zero address is not a device');
  return bytes;
}

/** The address of a secp256k1 public key: the low 20 bytes of keccak256 of the
 *  64-byte big-endian x || y. */
export function evmAddressOf(pk: { x: bigint; y: bigint }): Uint8Array {
  const point = secp256k1.Point.fromAffine({ x: pk.x, y: pk.y });
  point.assertValidity();
  return keccak_256(point.toBytes(false).subarray(1)).subarray(12);
}

const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';

/** Base58 (Bitcoin alphabet), the form Solana shows a public key in. */
export function base58Encode(bytes: Uint8Array): string {
  let zeros = 0;
  while (zeros < bytes.length && bytes[zeros] === 0) zeros++;
  let n = bigBE(bytes);
  let out = '';
  while (n > 0n) { out = B58[Number(n % 58n)] + out; n /= 58n; }
  return '1'.repeat(zeros) + out;
}

/** Strict base58: alphabet only, and the canonical encoding of its bytes. */
export function base58Decode(text: string, length: number): Uint8Array {
  if (!text || ![...text].every((c) => B58.includes(c))) throw new Error('descriptor: not base58');
  let zeros = 0;
  while (zeros < text.length && text[zeros] === '1') zeros++;
  let n = 0n;
  for (const c of text.slice(zeros)) n = n * 58n + BigInt(B58.indexOf(c));
  const tail: number[] = [];
  while (n > 0n) { tail.unshift(Number(n & 0xffn)); n >>= 8n; }
  const out = Uint8Array.from([...new Array(zeros).fill(0), ...tail]);
  if (out.length !== length) throw new Error(`descriptor: base58 value is ${out.length} bytes, not ${length}`);
  if (base58Encode(out) !== text) throw new Error('descriptor: non-canonical base58');
  return out;
}

/** A Solana public key: base58 text or the 32-byte RFC 8032 encoding.
 *  RFC 8032 strict decoding (canonical y < p, no "negative zero" x), and only
 *  keys of the prime-order subgroup other than the identity: small-order and
 *  mixed-order points are refused. Returns the 32 bytes. */
export function parseSolanaPublicKey(input: string | Uint8Array): Uint8Array {
  const bytes = typeof input === 'string' ? base58Decode(input, 32) : new Uint8Array(input);
  if (bytes.length !== 32) throw new Error('descriptor: a Solana public key is 32 bytes');
  let point;
  try { point = ed25519.Point.fromBytes(bytes, false); } catch (e: any) {
    throw new Error(`descriptor: not a canonical Ed25519 point (${e?.message ?? e})`);
  }
  if (!equalBytes(point.toBytes(), bytes)) throw new Error('descriptor: non-canonical Ed25519 encoding');
  if (point.isSmallOrder()) throw new Error('descriptor: Ed25519 key of small order (identity included)');
  if (!point.isTorsionFree()) throw new Error('descriptor: Ed25519 key of mixed order');
  return bytes;
}

/** The Curve25519Point of a Solana public key (base58 text or the 32-byte
 *  encoding), after parseSolanaPublicKey's strict checks: the argument the
 *  ed25519 class circuits take. */
export function solanaKeyPoint(input: string | Uint8Array): Curve25519Affine {
  const { x, y } = ed25519.Point.fromBytes(parseSolanaPublicKey(input), false).toAffine();
  return { x, y };
}

/** The 32-byte RFC 8032 encoding of a Curve25519Point given by coordinates,
 *  with the same strict rules: canonical coordinates (below p), on the
 *  curve, of prime order, not the identity. Small-order and mixed-order
 *  points are refused. */
export function solanaKeyFromPoint(p: Curve25519Affine): Uint8Array {
  if (typeof p !== 'object' || p === null || typeof p.x !== 'bigint' || typeof p.y !== 'bigint') {
    throw new Error('descriptor: an Ed25519 key point is { x, y } with bigint coordinates');
  }
  const P = ed25519.Point.Fp.ORDER;
  if (p.x < 0n || p.x >= P || p.y < 0n || p.y >= P) throw new Error('descriptor: Ed25519 coordinate not below p');
  if (p.x === 0n && p.y === 1n) throw new Error('descriptor: Ed25519 key of small order (the identity)');
  let point;
  try { point = ed25519.Point.fromAffine({ x: p.x, y: p.y }); point.assertValidity(); } catch (e: any) {
    throw new Error(`descriptor: not an Ed25519 point (${e?.message ?? e})`);
  }
  if (point.isSmallOrder()) throw new Error('descriptor: Ed25519 key of small order (identity included)');
  if (!point.isTorsionFree()) throw new Error('descriptor: Ed25519 key of mixed order');
  return parseSolanaPublicKey(point.toBytes());
}

type Curve = typeof secp256k1 | typeof p256;
function parseWeierstrass(curve: Curve, name: string, input: Uint8Array | { x: bigint; y: bigint }): { x: bigint; y: bigint } {
  let point;
  try {
    if (input instanceof Uint8Array) {
      if (input.length !== 33 && input.length !== 65) throw new Error('SEC1 key is 33 or 65 bytes');
      point = curve.Point.fromBytes(input);
    } else {
      const p = curve.Point.Fp.ORDER;
      if (input.x < 0n || input.x >= p || input.y < 0n || input.y >= p) throw new Error('coordinate not below p');
      point = curve.Point.fromAffine({ x: input.x, y: input.y });
    }
    point.assertValidity();
  } catch (e: any) {
    throw new Error(`descriptor: not a ${name} public key (${e?.message ?? e})`);
  }
  if (point.is0()) throw new Error(`descriptor: ${name} point at infinity`);
  const { x, y } = point.toAffine();
  return { x, y };
}

/** A secp256k1 key (SEC1 bytes or affine coordinates) and its envelope. */
export function parseK256Descriptor(key: Uint8Array | { x: bigint; y: bigint }, envelope: number): K256Descriptor {
  if (envelope !== 0 && envelope !== 1) throw new Error('descriptor: unknown k256 envelope');
  return { scheme: 'k256', ...parseWeierstrass(secp256k1, 'secp256k1', key), envelope };
}

/** Upstream's webauthnPolicy, its refusals reported as descriptor errors. */
function passkeyPolicy(rpId: string, origin: string) {
  try { return webauthnPolicy(rpId, origin); } catch (e: any) { throw new Error(`descriptor: ${e?.message ?? e}`); }
}

/** A passkey: its P-256 key, RP ID, and 21-byte origin. The RP ID must be the
 *  origin's host or a registrable parent of it (upstream's webauthnPolicy). */
export function parseP256Descriptor(key: Uint8Array | { x: bigint; y: bigint }, rpId: string, origin: string): P256Descriptor {
  const policy = passkeyPolicy(rpId, origin);
  return { scheme: 'p256', ...parseWeierstrass(p256, 'P-256', key), policy: { rpIdHash: policy.rp_id_hash, origin: policy.origin, rpId } };
}

/** A JubJub point: affine coordinates, or its 64-byte x_le || y_le encoding.
 *  Canonical coordinates, on the curve, of prime order (small-order and
 *  mixed-order points refused; the seam itself refuses small order). */
export function parseJubjubPoint(input: Uint8Array | { x: bigint; y: bigint }): JubjubDescriptor {
  let x: bigint, y: bigint;
  if (input instanceof Uint8Array) {
    if (input.length !== 64) throw new Error('descriptor: a JubJub point is 64 bytes (x_le || y_le)');
    x = bigLE(input.subarray(0, 32)); y = bigLE(input.subarray(32));
  } else ({ x, y } = input);
  const q = jubjub.Point.Fp.ORDER;
  if (x < 0n || x >= q || y < 0n || y >= q) throw new Error('descriptor: JubJub coordinate not canonical');
  if (x === 0n && y === 1n) throw new Error('descriptor: JubJub key of small order (the identity)');
  let point;
  try { point = jubjub.Point.fromAffine({ x, y }); point.assertValidity(); } catch (e: any) {
    throw new Error(`descriptor: not a JubJub point (${e?.message ?? e})`);
  }
  if (point.isSmallOrder()) throw new Error('descriptor: JubJub key of small order (identity included)');
  if (!point.isTorsionFree()) throw new Error('descriptor: JubJub key of mixed order');
  return { scheme: 'jubjub', x, y };
}

/** A readable device: its identity (20-byte address or 32-byte Ed25519 key)
 *  and the account's 32-byte blind. */
export function evmDescriptor(address: Uint8Array | string, blind: Uint8Array): EvmDescriptor {
  const a = typeof address === 'string' ? parseEvmAddress(address) : new Uint8Array(address);
  if (a.length !== 20) throw new Error('descriptor: an Ethereum address is 20 bytes');
  if (a.every((b) => b === 0)) throw new Error('descriptor: the zero address is not a device');
  if (blind.length !== 32) throw new Error('descriptor: a blind is 32 bytes');
  return { scheme: 'evm_eip712', address: a, blind: new Uint8Array(blind) };
}

export function solDescriptor(key: Uint8Array | string, blind: Uint8Array): SolDescriptor {
  if (blind.length !== 32) throw new Error('descriptor: a blind is 32 bytes');
  return { scheme: 'sol_ed25519', key: parseSolanaPublicKey(key), blind: new Uint8Array(blind) };
}

/** Re-checks a descriptor built elsewhere (for example decoded from a dApp's
 *  request) with the strict parsers above. Returns a fresh copy. */
export function checkDescriptor(d: Descriptor): Descriptor {
  switch (d.scheme) {
    case 'jubjub': return parseJubjubPoint({ x: d.x, y: d.y });
    case 'k256': return parseK256Descriptor({ x: d.x, y: d.y }, d.envelope);
    case 'p256': {
      const key = parseWeierstrass(p256, 'P-256', { x: d.x, y: d.y });
      if (!d.policy) return { scheme: 'p256', ...key };
      const { rpIdHash, origin, rpId } = d.policy;
      if (rpIdHash.length !== 32) throw new Error('descriptor: rp_id_hash is 32 bytes');
      if (origin.length !== WEBAUTHN_ORIGIN_BYTES) throw new Error(`descriptor: a passkey origin is ${WEBAUTHN_ORIGIN_BYTES} bytes`);
      // The bytes the wa-json134 circuit accepts in an origin (webauthn.compact).
      if (!origin.every((b) => b >= 0x21 && b <= 0x7e && b !== 0x22 && b !== 0x5c)) {
        throw new Error('descriptor: passkey origin is not visible ASCII without quotes or backslashes');
      }
      if (rpId !== undefined) {
        // The client knows the RP ID: it must hash to the shown value and fit
        // the origin, as upstream's webauthnPolicy requires.
        const p = passkeyPolicy(rpId, String.fromCharCode(...origin));
        if (!equalBytes(p.rp_id_hash, rpIdHash)) throw new Error('descriptor: rp_id_hash is not SHA-256 of the RP ID');
      }
      return { scheme: 'p256', ...key, policy: { rpIdHash: new Uint8Array(rpIdHash), origin: new Uint8Array(origin), ...(rpId !== undefined ? { rpId } : {}) } };
    }
    case 'evm_eip712': return evmDescriptor(d.address, d.blind);
    case 'sol_ed25519': return solDescriptor(d.key, d.blind);
  }
}

// ── Encoders: the class circuit and its arguments ───────────────────────────

/** A pure-circuit call: the circuit's name and its arguments, in the
 *  generated JavaScript's representation. `pick` is the index of the derived
 *  value when the circuit returns a tuple: the ed25519 class returns
 *  [key, value], the key it encoded from the point and the derived value. */
export interface DescriptorCall { circuit: string; args: unknown[]; pick?: number }

const pickOf = (cls: DescriptorClass): { pick?: number } => (cls === 'ed25519' ? { pick: 1 } : {});

const xyLE = (d: { x: bigint; y: bigint }): [Uint8Array, Uint8Array] => [bytesLE(d.x, 32), bytesLE(d.y, 32)];

/** The payload parts of a descriptor for a recipe, in circuit order. A
 *  `sol_ed25519` key is passed as its point, never as bytes. */
export function payloadParts(d: Descriptor, recipe: DescriptorRecipe): unknown[] {
  switch (d.scheme) {
    case 'jubjub': return xyLE(d);
    case 'k256': return [...xyLE(d), BigInt(d.envelope)];
    case 'p256': {
      if (recipe === 'grant-id') return xyLE(d);
      if (!d.policy) throw new Error('descriptor: a passkey device entry or boot commitment needs its policy');
      return [...xyLE(d), d.policy.rpIdHash, d.policy.origin];
    }
    case 'evm_eip712': return [d.address, d.blind];
    case 'sol_ed25519': return [solanaKeyPoint(d.key), d.blind];
  }
}

const contractAddress = (a: Uint8Array) => {
  if (a.length !== 32) throw new Error('descriptor: a contract address is 32 bytes');
  return { bytes: a };
};

/** The device entry of `d` in an account, at an epoch and use counter. An
 *  enrolment MUST pass the account's current device_epoch and counter 0. */
export function entryCall(d: Descriptor, account: Uint8Array, epoch: bigint, counter: bigint): DescriptorCall {
  return {
    circuit: `derive_descriptor_entry_${DESCRIPTOR_CLASS.device[d.scheme]}`,
    args: [padTag(DESCRIPTOR_TAGS.device[d.scheme]), contractAddress(account), ...payloadParts(d, 'device'), epoch, counter],
    ...pickOf(DESCRIPTOR_CLASS.device[d.scheme]),
  };
}

/** The boot commitment of `d` under a salt. */
export function bootCall(d: Descriptor, salt: Uint8Array): DescriptorCall {
  if (salt.length !== 32) throw new Error('descriptor: a salt is 32 bytes');
  return {
    circuit: `derive_descriptor_boot_${DESCRIPTOR_CLASS.boot[d.scheme]}`,
    args: [padTag(DESCRIPTOR_TAGS.boot[d.scheme]), salt, ...payloadParts(d, 'boot')],
    ...pickOf(DESCRIPTOR_CLASS.boot[d.scheme]),
  };
}

/** The grant id of grantee `d` in an account, for an origin_hash and slot. */
export function grantIdCall(d: Descriptor, account: Uint8Array, originHash: Uint8Array, slot: bigint): DescriptorCall {
  if (originHash.length !== 32) throw new Error('descriptor: origin_hash is 32 bytes');
  return {
    circuit: `derive_descriptor_grant_id_${DESCRIPTOR_CLASS['grant-id'][d.scheme]}`,
    args: [padTag(DESCRIPTOR_TAGS['grant-id'][d.scheme]), contractAddress(account), ...payloadParts(d, 'grant-id'), originHash, slot],
    ...pickOf(DESCRIPTOR_CLASS['grant-id'][d.scheme]),
  };
}

/** Runs a call through a `pureCircuits` object that exports the module. */
export function derive(pureCircuits: Record<string, any>, call: DescriptorCall): Uint8Array {
  const f = pureCircuits[call.circuit];
  if (typeof f !== 'function') throw new Error(`descriptor: ${call.circuit} is not exported by these circuits`);
  const r = f(...call.args);
  return call.pick === undefined ? r : r[call.pick];
}

// ── Decoder: circuit arguments back to a checked descriptor ─────────────────

/** Decodes the tag and payload parts of a class call (as payloadParts
 *  returns them) into a descriptor, then checks the key strictly. Refuses an
 *  unregistered tag, a tag of another recipe than `recipe`, parts of the
 *  wrong number or width, and a Solana key given as anything but a point. */
export function decodeDescriptor(recipe: DescriptorRecipe, tag: Uint8Array, parts: unknown[]): Descriptor {
  const t = tagOf(tag);
  if (t.recipe !== recipe) throw new Error(`descriptor: ${t.text} is a ${t.recipe} tag, not a ${recipe} tag`);
  const bytes = (v: unknown, n: number, what: string): Uint8Array => {
    if (!(v instanceof Uint8Array) || v.length !== n) throw new Error(`descriptor: ${what} must be ${n} bytes`);
    return new Uint8Array(v);
  };
  const want = (n: number) => { if (parts.length !== n) throw new Error(`descriptor: ${t.text} takes ${n} payload parts, got ${parts.length}`); };
  switch (t.scheme) {
    case 'jubjub':
      want(2);
      return parseJubjubPoint(new Uint8Array([...bytes(parts[0], 32, 'x'), ...bytes(parts[1], 32, 'y')]));
    case 'k256': {
      want(3);
      const env = parts[2];
      if (env !== 0n && env !== 1n) throw new Error('descriptor: unknown k256 envelope');
      return parseK256Descriptor({ x: bigLE(bytes(parts[0], 32, 'x')), y: bigLE(bytes(parts[1], 32, 'y')) }, Number(env));
    }
    case 'p256': {
      if (recipe === 'grant-id') {
        want(2);
        // A p256 grant id binds the key only; the RP is a scope field.
        return { scheme: 'p256', ...parseWeierstrass(p256, 'P-256', { x: bigLE(bytes(parts[0], 32, 'x')), y: bigLE(bytes(parts[1], 32, 'y')) }) };
      }
      want(4);
      return checkDescriptor({
        scheme: 'p256', x: bigLE(bytes(parts[0], 32, 'x')), y: bigLE(bytes(parts[1], 32, 'y')),
        policy: { rpIdHash: bytes(parts[2], 32, 'rp_id_hash'), origin: bytes(parts[3], WEBAUTHN_ORIGIN_BYTES, 'origin') },
      });
    }
    case 'evm_eip712':
      want(2);
      return evmDescriptor(bytes(parts[0], 20, 'address'), bytes(parts[1], 32, 'blind'));
    case 'sol_ed25519':
      want(2);
      return solDescriptor(solanaKeyFromPoint(parts[0] as Curve25519Affine), bytes(parts[1], 32, 'blind'));
  }
}

// ── Display ──────────────────────────────────────────────────────────────────

/** The byte order a client SHOWS a curve coordinate in (decision Q29 of AA
 *  00067, the convention of the frozen approvals): secp256k1 and P-256
 *  coordinates big-endian, as SEC1 and every wallet and tool show them;
 *  JubJub coordinates little-endian, Midnight's own encoding and the bytes
 *  the recipes bind (`x_le ‖ y_le`). Field values, which no descriptor
 *  carries, are shown little-endian under the same decision. */
export const COORDINATE_DISPLAY_ORDER: Readonly<Record<'jubjub' | 'k256' | 'p256', 'little-endian' | 'big-endian'>> = Object.freeze({
  jubjub: 'little-endian',
  k256: 'big-endian',
  p256: 'big-endian',
});

/** A coordinate as shown: `0x` and 64 lowercase hex digits, in the byte order
 *  of COORDINATE_DISPLAY_ORDER for its scheme. */
export function coordinateHex(scheme: keyof typeof COORDINATE_DISPLAY_ORDER, v: bigint): string {
  const order = COORDINATE_DISPLAY_ORDER[scheme];
  if (!order) throw new Error(`descriptor: ${scheme} has no coordinates`);
  return '0x' + toHex(order === 'little-endian' ? bytesLE(v, 32) : bytesBE(v, 32));
}

/** One shown line: a fixed label and its value in full. */
export interface DescriptorLine { label: string; value: string; verifiableByEye: boolean }

/** The lines a client shows for a descriptor, the same values the frozen
 *  approvals show. Keys are shown in full: an EVM address in EIP-55 form, a
 *  Solana key in base58 and hex, a passkey origin as text, and coordinates
 *  per COORDINATE_DISPLAY_ORDER (Q29: secp256k1 and P-256 big-endian, JubJub
 *  little-endian). `rp_id_hash` and the blind are the two labelled hash-like
 *  values; the client shows the RP ID beside the RP hash when it knows it. */
export function describeDescriptor(recipe: DescriptorRecipe, d: Descriptor): DescriptorLine[] {
  const tag = { label: 'Scheme tag', value: DESCRIPTOR_TAGS[recipe][d.scheme], verifiableByEye: true };
  const coord = (name: string, scheme: keyof typeof COORDINATE_DISPLAY_ORDER, v: bigint) =>
    ({ label: name, value: coordinateHex(scheme, v), verifiableByEye: false });
  switch (d.scheme) {
    case 'jubjub': return [tag, coord('JubJub key x', 'jubjub', d.x), coord('JubJub key y', 'jubjub', d.y)];
    case 'k256': return [tag, coord('secp256k1 key x', 'k256', d.x), coord('secp256k1 key y', 'k256', d.y),
      { label: 'Signing envelope', value: d.envelope === 0 ? '0 (SHA-256 of the challenge)' : '1 (dApp-connector signData)', verifiableByEye: false }];
    case 'p256': {
      const lines: DescriptorLine[] = [tag, coord('Passkey key x', 'p256', d.x), coord('Passkey key y', 'p256', d.y)];
      if (recipe !== 'grant-id' && d.policy) {
        lines.push({ label: 'Passkey origin', value: String.fromCharCode(...d.policy.origin), verifiableByEye: true });
        lines.push({ label: 'Passkey RP (hash)', value: '0x' + toHex(d.policy.rpIdHash) + (d.policy.rpId ? ` (RP ID ${d.policy.rpId}, shown by this client)` : ''), verifiableByEye: false });
      }
      return lines;
    }
    case 'evm_eip712': return [tag, { label: 'Ethereum address', value: evmChecksumAddress(d.address), verifiableByEye: true },
      { label: 'Device privacy salt', value: '0x' + toHex(d.blind), verifiableByEye: false }];
    case 'sol_ed25519': return [tag, { label: 'Solana public key', value: base58Encode(d.key), verifiableByEye: true },
      { label: 'Solana public key (hex)', value: toHex(d.key), verifiableByEye: true },
      { label: 'Device privacy salt', value: '0x' + toHex(d.blind), verifiableByEye: false }];
  }
}

/** A 21-byte passkey origin's or a 32-byte label's grant origin_hash: SHA-256
 *  of the padded origin tag and the fixed-width bytes (the module's recipe). */
export function grantOriginHash(fixedWidth: Uint8Array): Uint8Array {
  if (fixedWidth.length !== WEBAUTHN_ORIGIN_BYTES && fixedWidth.length !== 32) {
    throw new Error('descriptor: a grant origin is a 21-byte passkey origin or a 32-byte label');
  }
  return sha256(new Uint8Array([...padTag(GRANT_ORIGIN_TAG), ...fixedWidth]));
}

/** A readable grantee's 32-byte origin label: visible words separated by
 *  single spaces, zero-padded (the module's label_text_32 grammar). */
export function grantLabel(text: string): Uint8Array {
  if (!/^[\x21-\x7e]+(?: [\x21-\x7e]+)*$/.test(text)) throw new Error('descriptor: a label is visible words separated by single spaces');
  const b = TEXT.encode(text);
  if (b.length > 32) throw new Error('descriptor: a label is at most 32 bytes');
  const out = new Uint8Array(32);
  out.set(b);
  return out;
}
