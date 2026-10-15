---
MIP: X
Title: ECDSA Authorisation for Custody Accounts
Authors:
  - Nicolas Di Prima (NicolasDP)
Status: Draft
Category: Standards
Created: 2026-08-25
Requires: MIP-0012, MIP-0013
Replaces: N/A
---

<!--
Licensed under the Apache License, Version 2.0 (the "License"); you may
not use this file except in compliance with the License. You may obtain
a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
-->

## Abstract

Independent wallets and custody contracts need to agree on exactly what
an ECDSA credential signs and what the circuit verifies. A mismatched
hash layer, envelope selector or WebAuthn policy breaks that boundary.
This successor-extension working draft records the current secp256k1
(`k1`) and WebAuthn secp256r1 (`r1`) constructions and proposes bounded
verification obligations. Its value is interoperable approval without
giving the signing key to the prover. It is not yet a complete,
independently implementable standard.

## 1. Scope and conformance delta

[MIP-0013 §10](https://github.com/midnightntwrk/midnight-improvement-proposals/blob/main/mips/mip-0013-account-authorisation.md#10-versioning)
permits a successor under a **new or revising MIP**. Numbering versus
amendment is editorial. AUTH-1 explicitly requires Schnorr: ECDSA routes
therefore require a conformance delta, replacing its signature relation,
key encodings and challenge construction with those below.

Device routes MUST preserve active-epoch membership, single-use entry
rolling, account-nonce advancement, last-device protection and atomic
abort. This preserves state invariants rather than MIP-0013's literal
gate order: the r1 reference computes the challenge and verifies before
rolling the entry. Mixed-scheme devices share the account's lifecycle
state; scheme-specific commitments distinguish their entries.

A scheme does not confer device or grant authority. Viewing and recovery
are separate capabilities. Grant lifecycle, scope and replay rules belong
to the [scoped-grants companion](mip-xxxx-scoped-grants.md).

MUST, MUST NOT, SHOULD and MAY use RFC 2119 meanings. Requirements below
are proposed obligations; reference recipes describe existing bytes.

## 2. Reference signing bytes

Here `H` is SHA-256 and `||` is byte concatenation. `pad(w, tag)` is
ASCII without embedded NUL, followed by zero bytes to exactly width `w`;
tags MUST fit without truncation. Salt, account address and hashes are
32 bytes. Salt is fresh per account. Coordinates `x`, `y` are canonical
32-byte little-endian integers; `epoch` is LE4 and `counter` is LE8.

### Boot and device commitments

The existing boot/device recipes use **v2** for both ECDSA schemes:

```text
k1_boot   = H(pad(32, "midnight:account:boot:k1:v2") || salt || x || y || envelope)
k1_device = H(pad(32, "midnight:account:device:k1:v2") || account || x || y || envelope || epoch || counter)
r1_boot   = H(pad(32, "midnight:account:boot:r1:v2") || salt || x || y || rpIdHash || origin)
r1_device = H(pad(32, "midnight:account:device:r1:v2") || account || x || y || rpIdHash || origin || epoch || counter)
```

`envelope` is one byte (`Uint<8>`). `rpIdHash` is 32 bytes; `origin` is
the exact origin bytes, 21 bytes in the current reference profile.
Signed origins are never padded. These recipes bind the k1 envelope
and r1 RP/origin policy to the credential.

Sources: [k1 commitments](../../../contract/contracts/account.compact#L439-L503),
[r1 commitments](../../../contract/contracts/account-p256.compact#L28-L45).

### Device-operation challenge

Operation tags retain `midnight:account:auth:k1:v1:<operation>` and
`midnight:account:auth:r1:v1:<operation>`. The shared device-route schema is:

```text
dst = H(pad(64, operation_tag))
c   = H(dst || account || x || y || encode(operation_values) || auth_nonce_LE8)
```

The first element is the **32-byte tag hash**, not the padded tag.
`encode(operation_values)` denotes the operation's typed Compact
encoding, including consumed witness values in the specified order.
The circuit MUST recompute `c` from the actual consumed inputs and the
pre-increment account nonce.
Consumed private values MUST be bound even when secret; the exclusion
is authorising material, not all secrets. A digest may substitute for
declared operation values only when the circuit recomputes it from
those values, as `issue_grant` does for its scope digest. ECDSA
challenges contain neither signature material nor a grinding nonce.

This schema is not a complete per-operation serialization specification.
The specification work in section 6 must supply all types, widths,
ordering and independent vectors, including native Fields and points.
Current recipes are in [k1 challenge builders](../../../contract/contracts/account.compact#L712)
and [r1 builders](../../../contract/contracts/account-p256.compact#L74-L174);
[grant issuance](../../../contract/contracts/account-p256.compact#L224-L241)
shows the recomputed-digest substitution.

Grantee calls use their own challenge domain and state. The
[r1 grant builder](../../../contract/contracts/account-p256.compact#L278-L313)
hashes, in order, the padded-tag hash, account, x, y, grant ID,
`issued_at` (`Uint<64>`, LE8), typed operation inputs including consumed
witnesses, and `g.nonce` (LE8). `issued_at` is not the 32-bit revocation
generation. Grantee calls do not consume a device entry or use device
`auth_nonce`; the companion specifies their authorisation rules.

### Digest passed to ECDSA verification

- **k1 envelope 0:** `H(c)`.
- **k1 envelope 1:** `H(ASCII("midnight_signed_message:32:") || c)`;
  the prefix is exactly **27 bytes**. Unknown selectors are rejected.
- **r1:** `H(authenticatorData || H(exact clientDataJSON))`, with the
  WebAuthn challenge equal to `c`, encoded as 43 unpadded base64url
  characters in client data.

k1 **never verifies the raw challenge directly**. Its authorisation
API carries the enrolled envelope selector. See
[digest construction](../../../contract/contracts/account.compact#L541-L547),
[gate](../../../contract/contracts/account.compact#L881-L907),
[wallet signer](../../../contract/src/wallet/signer.ts#L278-L350) and
[independent raw-challenge rejection](../../../contract/src/tests/unit-offline.ts#L324-L339).

Both schemes MUST enforce canonical coordinates in the curve's base
field, on-curve non-identity keys and canonical scalars `1 <= r,s < n`.
Verification interprets the digest
big-endian modulo the curve order, rejects an identity result, and
checks `R.x mod n == r`. Both high-S and low-S are accepted. Equivalent
signatures remain bound to the same single execution by replay state;
signature bytes are private authorising material, not operation IDs.

## 3. Bounded WebAuthn verification

Named, versioned, bounded profiles are permitted. Each MUST declare
accepted forms and byte lengths, required fields and boundary checks,
flag/extension rules, wire-to-circuit conversions and conformance
vectors. Wallet and contract MUST establish compatible capabilities
before enrolment or grant issuance.

Every r1 gate MUST enforce in-circuit:

1. The authorised key, recomputed operation challenge, `webauthn.get`
   type, challenge encoding, and expected RP hash and signed origin.
   RP/origin policy comes from authenticated configuration or credential
   binding, never unchecked prover input. For grants, the signed origin
   must also match the companion's committed `origin_hash`.
2. User presence and the authorised UV policy, together with declared
   flags, cross-origin/top-origin and extension rules, including
   BS-implies-BE. The signed authenticator header is RP hash32, flags1,
   signCount4 (big-endian). Any accepted suffix requires specified checks.
3. Both hash layers over the **complete, exact signed bytes** and ECDSA
   verification. Fixed-shape reconstruction is permitted if every byte
   is constrained. Buffered implementations MUST constrain logical
   lengths and exclude unused capacity. Hashes, offsets and lengths
   supplied as advice MUST be independently constrained.

A full-envelope profile constrains its entire accepted serialization.
A profile using the
[W3C limited-verification algorithm](https://www.w3.org/TR/webauthn-3/#clientdatajson-verification)
MUST identify that algorithm and enforce its field/boundary checks
while hashing the full message. It does not establish arbitrary
trailing JSON syntax; profiles MUST state that suffix guarantee
accurately. Wallet-side parsing adds no proof guarantee. Unsupported
assertions MUST be rejected, never truncated, reserialized or padded
to fit.

**Downgrade protection:** every reachable verifier accepting a credential
MUST enforce its authorised policy. One installed verifier is insufficient
if a weaker sibling accepts the same credential. A single immutable
profile, a common enforced floor or authenticated routing may suffice;
otherwise credential/routing binding is required. This does not mandate
a stored profile ID. Updates MUST preserve policy or use an authorised
policy-change procedure.

**UV recommendation:** UP+UV on every WebAuthn gate is the simplest policy
and matches the reference. This recommendation is not an adopted common
floor. Requiring UV only for asset release leaves UP-only `add_device`,
`issue_grant` or recovery-authority replacement able to enable indirect
spending; any weaker proposal must address that escalation.

`signCount` is signed but MUST NOT supply account replay protection;
device/grant state supplies it. ES256 verification does not establish
hardware custody, device binding or a particular biometric.

## 4. Current evidence and its limits

Compact 0.35 provides native P-256 verification. The
[reference `wa-json134` profile](../../../contract/WEBAUTHN.md#supported-profile-wa-json134)
accepts exactly 134-byte client JSON, a 21-byte origin and 37-byte
authenticator data: fixed field order and punctuation, unescaped ASCII
origin, `crossOrigin:false`, no extra members or extensions, and flags
5, 13 or 29 (UP+UV). It is
implementation-specific evidence, not an adopted W3C or MIP baseline.
The [verifier](../../../contract/contracts/webauthn.compact) and
[independent recipe checks](../../../contract/src/tests/p256-offline.ts)
document that construction.

One [live Safari localhost account-key rotation](../../../contract/evidence/p256-webauthn/browser-flow.md)
was accepted. This is separate from software fixtures, grant tests and
caller-binding validation; it establishes no broader browser coverage.
Local runtime malformed-key negatives do not demonstrate native proof
constraints. Key-admissibility enforcement still needs the review below.

The standalone #179 bounded256/origin96 experiment saved **zero** proof
or verifier-key bytes (6,364/2,745 unchanged), with 8.9× rows and 8.1×
prover-key bytes. Its fee-unbalanced software proofs were verified in
memory, not node-accepted account calls; see
[pinned findings](https://github.com/midnightntwrk/passport/blob/cd08b4b104668833654a7de3b2a96f252b38f950/experiments/webauthn-variable-json/FINDINGS.md).

The reference's specialised circuits use a **15,000-verifier-byte
deployment-wave budget**; implementation costs are recorded in
[P256-MEASUREMENTS](../../../contract/P256-MEASUREMENTS.md).

## 5. Compatibility

Existing bytes remain the reference recipes. Changing a committed
preimage requires explicit versioning and migration; profile metadata
cannot silently change it. This draft sets no k1 retirement policy.

[MIP-0021](https://github.com/midnightntwrk/midnight-improvement-proposals/blob/main/mips/mip-0021-domain-separation.md)
is Proposed and explicitly rejects a central registry. Existing zero
padding, colon-version tags and underscore operation names conflict with
its convention. Editors must reconcile these constructions without
silently migrating cryptographic bytes.

## 6. Remaining specification decisions

| Item | Required resolution |
|---|---|
| Complete signing recipes | Pin per-operation typed encodings and link existing byte-exact vectors; identify any uncovered cases. |
| Security policy | Decide the common UV floor and specify authorised policy binding across verifier routes without prescribing storage layout. |
| k1 support | Continued coexistence is recommended; justify any retirement using actual consumer and migration evidence, not P-256 availability alone. |
| Review | Map key/scalar admissibility, profile boundary guarantees and the high-S/replay argument to enforcing layers and pinned versions; retain unresolved cryptographic questions explicitly. |
| Editorial alignment | Agree successor versus amendment and reconcile MIP-0021 tags with explicit compatibility treatment. |

## 7. Readable EIP-712 arm (`evm_eip712`)

This section records a third ECDSA construction: an Ethereum
externally owned account (any EIP-712 wallet) as a device or a
grantee. Its curve is secp256k1, as for k1; its signing bytes and
key binding depart from section 2 as stated here. Byte contract,
frozen vectors and acceptance policy:
[EVM-EIP712](../../../contract/EVM-EIP712.md); costs:
[EVM-EIP712-MEASUREMENTS](../../../contract/EVM-EIP712-MEASUREMENTS.md).

**Conformance delta.** Device routes keep the state invariants of
section 1 (active-epoch membership, single-use entry rolling,
account-nonce advancement, last-device protection, atomic abort) in
the r1 order: membership, verification, roll, nonce. Grantee routes
follow the [scoped-grants companion](mip-xxxx-scoped-grants.md): the
grant record's `issued_at` and nonce, never the device `auth_nonce`.

**Signing bytes: no challenge hash.** Section 2's challenge `c` is
replaced by EIP-712 typed data, one primary type per operation and
role (13 device, 3 grantee). Its members are every operand and every
consumed witness value, in full; the circuit recomputes the struct
hash and verifies ECDSA over
`keccak256(0x19 || 0x01 || domainSeparator || hashStruct(message))`.
The domain is `EIP712Domain(string name,string version,address
verifyingContract)` with name `Midnight Passport Account`, version
`1`, and `verifyingContract` the low 20 bytes of `keccak256` of the
account address; it has no `chainId` and no salt (see Network
below). Consumed private values that ledger state already pins (the
signer's blind and use counter, `scope_salt`, the spent opening, a
grantee's pinned recipient and coin bound) are verified against
state rather than shown. The other key of `add_device`,
`remove_device`, `issue_grant` and `revoke_grant` is shown as a
readable descriptor (scheme tag text and key payload) from which the
circuit derives that scheme's entry or grant ID with the scheme's own
recipe; an unregistered tag is refused. A Solana key is taken as its
point: the circuit derives and shows its 32-byte encoding and refuses
the identity.

**The four labelled values.** Exactly four hash-like values may
appear, each under a fixed member name, none granting authority: a
k1/jubjub grantee's `origin_hash` (`siteLabelHash`; the client shows
the client ID beside it); a passkey's `rpIdHash` (`passkeyRpHash`;
the RP ID may be a registrable parent of the origin host); a target
device's blind (`privacySalt`); and the literal entry of a
revocation-only `remove_device` (`RemoveUnknownDevice.entry`, under
"Removes a device this wallet cannot identify"). Authority-granting
types carry circuit-fixed effect lines, and enumerated members (the
recipient kind, the k1 envelope) are shown as circuit-fixed text
labels selected by the value.

**Commitments and tags.** With `H` SHA-256, `A` the account and
`blind` per Blinding below:

```text
evm_boot   = H(pad(32, "midnight:account:boot:evm:v1") || salt || address || blind)
evm_device = H(pad(32, "midnight:account:device:evm:v1") || A || address || blind || epoch || counter)
evm_grant  = H(pad(32, "midnight:account:grant:id:evm:v1") || A || address || blind || origin_hash || slot)
blind      = H(pad(32, "midnight:account:blind:evm:v1") || r || s)
```

`address` is the 20-byte `secp256k1EthereumAddress(pk)`; `epoch` is
LE4, `counter` LE8, `slot` one byte. These tags follow the existing zero-padded colon-version convention and so
share the MIP-0021 conflict noted in section 5.

**Key and scalar admissibility.** Every path derives the address from
the presented point, never from the caller. The point at infinity is
refused in both encodings; `r != 0` and `s != 0` are asserted; both
S forms are accepted, and single-use entries make the twin inert.
Non-canonical coordinate representations are refused by the honest
toolchain's input decoding, not by a constraint; a second 32-byte
representation exists only for coordinates below about 2^32, and
canonicity of the foreign-field cast remains an open review item.

**Wallet-key grantees.** A grantee key is a wallet key reused across
sites, not a key bound to one origin. Its `siteLabel` is a label the
issuer chose and the grantee's wallet shows, not an authenticated
origin. The compensation is readable per-call consent: every grantee
call shows its amount, recipient, coin and grant frame.

**Network.** The contract binds no network, and circuits cannot read
the network ID. Because the ledger derives a contract address from
its deploy alone, a replayed deploy on another network yields an
account at the same address, and an approval verifies there whenever
that clone reaches the state it was signed against. No in-contract
value can tell the clone apart. Clients MUST use random deploy
nonces; binding the network ID belongs to the ledger, where it is
proposed.

**Blinding.** Device entries, boot commitments and grant IDs are
blinded with a per-account secret: the blind above, taken over the
low-S `r || s` of a deterministic `personal_sign` signature on a
readable request naming Midnight Passport, the network, the wallet
address and an account index, and warning that it reveals the
account's privacy key. The request's EIP-191 preimage (`0x19 0x45`)
is disjoint from every authorisation's (`0x19 0x01`). Clients MUST
sign it twice and refuse a wallet whose two signatures differ. The
ledger then holds no value a known address can be tested against;
whoever obtains the signature learns the blind (a privacy loss, not
an authority). A grantee's blind, which the issuer must know, comes
from a separate request naming the role and the issuing account (no
account index), so an issuer never learns a device blind and each
issuer gets its own.

**Provenance residual.** Showing a key in full does not prove whose
it is. Approving an attacker-supplied key or recovery material grants
what the effect line states. Mitigations: circuit-fixed effect lines,
the new device's client rendering the identical descriptor for
comparison (MIP-0013 S7), and recovery material from the client's own
guardian ceremony. The EVM address, a passkey origin and a 32-byte
Ed25519 key can be compared by eye; k1, jubjub and passkey public
keys are shown only.

## Copyright Waiver

This document is licensed under the Apache License, Version 2.0, and
its authors have signed the Midnight Foundation Contributor License
Agreement. Portions of this document were drafted with the assistance
of a large language model; the named authors reviewed and are
accountable for its entire content.
