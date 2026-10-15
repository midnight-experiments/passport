// Readable values (AA 00067 Q43) — the client's copy of the rendering
// module's magnitude and exact words (contracts/modules/WalletArmRendering.compact,
// `uint128_magnitude_text`, `expiry_text`, `rp_hash_text`).
//
// Every amount and cap is shown in base units in full AND with its order of
// magnitude, "~d.dd x 10^e": the exponent is the number of digits after the
// first, the mantissa the first three digits, truncated (never rounded);
// zero is "0". 2^128 - 1 and 2^128 - 2 both read "~3.40 x 10^38", so a huge
// value reads as huge whatever it is. A fixed word replaces a value only
// where the value has an exact protocol meaning: a grant expiry of 0 is
// "never", an all-zero passkey RP hash is "not applicable".
//
// The circuit space-pads each text to its field's width (13, 20 and 64
// bytes); the *Bytes functions return exactly those bytes, the plain ones
// the visible text.

/** The width the circuit pads a magnitude to (bytes). */
export const MAGNITUDE_TEXT_WIDTH = 13;
/** The width of a Uint<64> decimal field, and of the expiry text. */
export const EXPIRY_TEXT_WIDTH = 20;
/** The width of a 32-byte hash in hex, and of the RP hash text. */
export const RP_HASH_TEXT_WIDTH = 64;
/** A grant expiry of 0: the grant never expires. */
export const NEVER_TEXT = 'never';
/** An all-zero passkey RP hash: no passkey is involved. */
export const NOT_APPLICABLE_TEXT = 'not applicable';

const UINT128_MAX = (1n << 128n) - 1n;
const UINT64_MAX = (1n << 64n) - 1n;

const asBig = (v: bigint | number, what: string, max: bigint): bigint => {
  if (typeof v === 'number' && !Number.isSafeInteger(v)) throw new Error(`rendering: ${what} must be an integer`);
  const n = BigInt(v);
  if (n < 0n || n > max) throw new Error(`rendering: ${what} out of range`);
  return n;
};
const padded = (s: string, w: number): Uint8Array => new TextEncoder().encode(s.padEnd(w, ' '));

/** The magnitude of a Uint<128> amount or cap: "~d.dd x 10^e", or "0". */
export function magnitudeText(value: bigint | number): string {
  const v = asBig(value, 'an amount', UINT128_MAX);
  if (v === 0n) return '0';
  let e = 0;
  for (let x = v; x >= 10n; x /= 10n) e++;
  // The first three digits, truncated: scale the value to three digits.
  const three = e >= 2 ? v / 10n ** BigInt(e - 2) : v * 10n ** BigInt(2 - e);
  const m = three.toString();
  return `~${m[0]}.${m.slice(1, 3)} x 10^${e}`;
}

/** The magnitude as the circuit shows it: space-padded to 13 bytes. */
export const magnitudeTextBytes = (value: bigint | number): Uint8Array => padded(magnitudeText(value), MAGNITUDE_TEXT_WIDTH);

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
