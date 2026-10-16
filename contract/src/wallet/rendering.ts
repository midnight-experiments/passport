// Readable values (AA 00067 Q43 A', revised by Q44 A'') — the client's copy
// of the rendering module's exact words (contracts/modules/WalletArmRendering.compact,
// `expiry_text`, `rp_hash_text`).
//
// A fixed word replaces a value only where the value has an exact protocol
// meaning: a grant expiry of 0 is "never", an all-zero passkey RP hash is
// "not applicable". Every other value is shown as before; amounts and caps
// stay in base units in full (Q44 A'' removed the Q43 magnitude).
//
// The circuit space-pads each text to its field's width (20 and 64 bytes);
// the *Bytes functions return exactly those bytes, the plain ones the
// visible text.

/** The width of a Uint<64> decimal field, and of the expiry text. */
export const EXPIRY_TEXT_WIDTH = 20;
/** The width of a 32-byte hash in hex, and of the RP hash text. */
export const RP_HASH_TEXT_WIDTH = 64;
/** A grant expiry of 0: the grant never expires. */
export const NEVER_TEXT = 'never';
/** An all-zero passkey RP hash: no passkey is involved. */
export const NOT_APPLICABLE_TEXT = 'not applicable';

const UINT64_MAX = (1n << 64n) - 1n;

const asBig = (v: bigint | number, what: string, max: bigint): bigint => {
  if (typeof v === 'number' && !Number.isSafeInteger(v)) throw new Error(`rendering: ${what} must be an integer`);
  const n = BigInt(v);
  if (n < 0n || n > max) throw new Error(`rendering: ${what} out of range`);
  return n;
};
const padded = (s: string, w: number): Uint8Array => new TextEncoder().encode(s.padEnd(w, ' '));

/** A grant's expiry (block time, seconds): "never" for 0, else the decimal seconds. */
export function expiryText(value: bigint | number): string {
  const v = asBig(value, 'an expiry', UINT64_MAX);
  return v === 0n ? NEVER_TEXT : v.toString(10);
}

/** The expiry as the circuit shows it: space-padded to 20 bytes. */
export const expiryTextBytes = (value: bigint | number): Uint8Array => padded(expiryText(value), EXPIRY_TEXT_WIDTH);

/** A grant's passkey RP hash: "not applicable" when all 32 bytes are zero, else its 64 hex digits. */
export function rpHashText(h: Uint8Array): string {
  if (!(h instanceof Uint8Array) || h.length !== 32) throw new Error('rendering: an RP hash is 32 bytes');
  return h.every((b) => b === 0) ? NOT_APPLICABLE_TEXT : Array.from(h, (b) => b.toString(16).padStart(2, '0')).join('');
}

/** The RP hash as the circuit shows it: space-padded to 64 bytes. */
export const rpHashTextBytes = (h: Uint8Array): Uint8Array => padded(rpHashText(h), RP_HASH_TEXT_WIDTH);
