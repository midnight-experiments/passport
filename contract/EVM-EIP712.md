# The `evm_eip712` authorisation arm

**Byte contract AUTH-EIP712-PASSPORT-EVM-V1.** Signing bytes frozen 2026/10/15. All 16 circuits are in place and registered in `ARMS`; the measurement report is [EVM-EIP712-MEASUREMENTS.md](EVM-EIP712-MEASUREMENTS.md), the evidence is under [evidence/evm-eip712/](evidence/evm-eip712/).

An ordinary Ethereum account, for example MetaMask, acts as a Passport device or as a grantee. It authorises every operation by signing EIP-712 typed data. In that typed data, every operand and every consumed witness value is a member, shown by the wallet in full and recomputed by the circuit from exactly the values it executes. Nothing opaque is signed: there is no challenge hash and no fingerprint. Four labelled values are the only exception (section 6). The wallet needs no ETH and sends no Ethereum transaction.

| | |
|---|---|
| Circuits | `contracts/account-evm-eip712.compact` (the arm), `contracts/modules/EvmEip712.compact` (the codec) |
| Client | `src/wallet/signer-evm-eip712.ts` (wallet, device, blind, roster), `src/wallet/evm-eip712-codec.ts` (typed data) |
| Frozen vectors | `src/tests/vectors/evm-eip712-v1.json`: 53 positive and 16 negative vectors, hashes computed by viem 2.45.1 |
| Tests | `src/tests/evm-eip712-offline.ts`, `src/tests/evm-eip712-grants-offline.ts` and `src/tests/evm-eip712-recovery-sim.ts` (all three: `npm run test:evm_eip712-offline`), `src/tests/evm-eip712-viem.ts` (needs viem, see section 8), `src/tests/evm-eip712-prover.ts` (constraint-level negatives: `npm run test:evm_eip712`) |

## 1. Identity

The device is its 20-byte Ethereum address, `secp256k1EthereumAddress(pk) = keccak256(x_be ‖ y_be)[12..32]`, **blinded** (spec FR-013). Every recipe below is SHA-256 (`persistentHash`) over the plain concatenation. `A` is the account's 32-byte contract address, and `le4`/`le8` are little-endian `Uint<32>`/`Uint<64>`:

```
entry    = H(pad32("midnight:account:device:evm:v1")   ‖ A    ‖ address(20) ‖ blind(32) ‖ le4(epoch) ‖ le8(counter))
boot     = H(pad32("midnight:account:boot:evm:v1")     ‖ salt ‖ address(20) ‖ blind(32))
grant id = H(pad32("midnight:account:grant:id:evm:v1") ‖ A    ‖ address(20) ‖ blind(32) ‖ origin_hash(32) ‖ slot(1))
```

These are width class 52 of the shared descriptor module (`modules/WalletArmDescriptors.compact`). Every readable arm derives an `evm_eip712` target's entry with the same recipe.

Every path that admits a key takes the secp256k1 **point** and derives the address itself (spec FR-011). Before that, it refuses the point at infinity by its coordinates, which catches both encodings. A caller can never present an address without a key.

## 2. The blind

`blind = H(pad32("midnight:account:blind:evm:v1") ‖ r ‖ s)`, where `r ‖ s` is the low-S canonical form (big-endian, 32 bytes each) of the wallet's `personal_sign` signature (EIP-191 version `0x45`, Q25) over this readable request:

```
Midnight Passport account privacy key (v1)
Network: <network name>
Wallet: Ethereum address <EIP-55 address>
Account index: <0 … 4294967295>
Warning: this signature reveals the privacy key of this Passport account.
Anyone who obtains it can link this wallet to that account.
Sign it only in a Midnight Passport client you trust.
It authorises nothing: no transfer, no new device, no grant.
```

The procedure:

- The client asks for the signature **twice** and refuses the wallet if the two canonical forms differ. Such a wallet is non-deterministic (MPC, hedged nonces), so its blind could never be derived again.
- The client recovers the device's public point from the same signature and checks that it hashes to the wallet's address.
- The `personal_sign` hash preimage begins `0x19 0x45` (`0x19` and `'E'` of `"Ethereum Signed Message:\n"`), and every authorisation's hash preimage begins `0x19 0x01`. The preimages are disjoint, so the two digests coincide only on a keccak256 collision: a blind signature is never an authorisation, and an authorisation is never a blind signature. No circuit consumes a `personal_sign` digest.
- A restored client derives `blind_0 … blind_k` and finds its accounts by testing entries (`restoreEvmDevices`).
- As a **grantee**, the wallet signs a different request: `granteeBlindMessage` names the role ("grantee"), the network, the wallet and the issuing account's 32-byte address, and has no account index (Q39). Its first two lines differ from the device request's, so a grantee blind is never a device blind, and it is different for every issuing account (`enrolEvmGranteeBlind`, `EvmEip712Grantee.enrol`).

## 3. Domain

```
EIP712Domain(string name,string version,address verifyingContract)
name               "Midnight Passport Account"
version            "1"
verifyingContract  the low 20 bytes of keccak256(A)
```

There is no `chainId` and no `salt`. The contract holds no network value (Q4), and the cross-network clone argument is in section 10. The circuit recomputes the domain separator on every call: it is constant per account, but a cache would need a ledger or constructor field (FR-001).

What the wallet signs:

```
digest = keccak256(0x19 ‖ 0x01 ‖ domainSeparator ‖ hashStruct(message))
```

## 4. Encoding

This is EIP-712 `encodeData`, one 32-byte word per member:

| Member type | Word |
|---|---|
| `bytes32` | the 32 bytes |
| `address` | 12 zero bytes ‖ the 20 bytes |
| `uint8`, `uint32`, `uint64`, `uint128` | big-endian, zero-extended |
| `bool` | 0 or 1 as a uint |
| `string`, `bytes` | keccak256 of the content |
| nested struct | its `hashStruct` |

The byte order of points and field elements follows Q29:

- secp256k1 and P-256 coordinates are big-endian (SEC1).
- JubJub coordinates and other `Field` values are little-endian, as the contract encodes them.

Text members:

- `scheme` is a registered tag's text, without its zero padding.
- `origin` is a passkey's exact 21-byte origin, which must be visible ASCII.
- `siteLabel` is a 32-byte zero-padded site label, shown with its zero bytes as spaces. It is 32 characters long. Its grammar makes the shown text one-to-one with the stored bytes: one or more visible words separated by single spaces, then zero bytes only.
- `effect` is a circuit-fixed line.

## 5. Types

There are 16 primary types, one per operation and role. The device role's 13 share the frame `bytes32 account, address device, uint64 authNonce`. The grantee role's 3 share `bytes32 account, address grantee, string siteLabel, uint8 slot, uint64 issuedAt, uint64 grantNonce`. A grantee's frame never carries `auth_nonce`.

| Circuit | Primary type |
|---|---|
| `withdraw_unshielded_with_evm_eip712` | `WithdrawUnshielded(bytes32 account,address device,uint64 authNonce,bytes32 color,uint128 amount,bytes32 recipient)` |
| `withdraw_shielded_with_evm_eip712` | `WithdrawShielded(…frame…,bytes32 color,uint128 amount,bytes32 recipient,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `withdraw_shielded_to_contract_with_evm_eip712` | `WithdrawShieldedToContract(…frame…,bytes32 color,uint128 amount,bytes32 recipientContract,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `append_inbox_with_evm_eip712` | `AppendInbox(…frame…,bytes entry)` |
| `rotate_enc_key_with_evm_eip712` | `RotateEncKey(…frame…,string effect,bytes32 newKey)` |
| `add_device_with_evm_eip712` | `AddDevice(…frame…,string effect,<Scheme>Device newDevice)` |
| `remove_device_with_evm_eip712` (descriptor) | `RemoveDevice(…frame…,<Scheme>Device target,uint32 targetEpoch,uint64 targetCounter)` |
| `remove_device_with_evm_eip712` (literal, Q20) | `RemoveUnknownDevice(…frame…,string effect,bytes32 entry)` |
| `issue_grant_with_evm_eip712` | `IssueGrant(…frame…,string effect,<Scheme>Grantee grantee,bool withdrawUnshielded,bool withdrawShielded,bool withdrawShieldedToContract,bool read,bytes32 color,uint8 recipientKind,bytes32 recipient,uint128 maxCoinValue,uint128 perCallCap,uint128 cap,uint64 expiresAt,bytes32 passkeyRpHash,bytes32 readKey,uint64 windowLength,uint128 windowCap,bool callerPinned,bytes32 caller)` |
| `revoke_grant_with_evm_eip712` | `RevokeGrant(…frame…,<Scheme>Grantee grantee)` |
| `revoke_all_grants_with_evm_eip712` | `RevokeAllGrants(…frame…)` |
| `publish_recovery_session_with_evm_eip712` | `PublishRecoverySession(…frame…,string effect,bytes32 recoveryKeyX,bytes32 recoveryKeyY,bytes32 sessionNonce,bytes32 phi1,bytes32 phi2,bytes32 phi3,bytes32 phi4,uint8 phiLength,bytes wrap)` |
| `recover_cancel_with_evm_eip712` | `CancelRecovery(…frame…)` |
| `withdraw_unshielded_with_grant_evm_eip712` | `WithdrawUnshieldedAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipient)` |
| `withdraw_shielded_with_grant_evm_eip712` | `WithdrawShieldedAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipient,bytes changeEntry,bytes32 encryptionKey,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `withdraw_shielded_to_contract_with_grant_evm_eip712` | `WithdrawShieldedToContractAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipientContract,bytes changeEntry,bytes32 encryptionKey,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |

The exact `encodeType` strings, 32 of them counting each descriptor scheme, are in the vector file under `typeStrings`.

The nested descriptor types follow Q28, one per target scheme. The parent's type string names the nested type, so the parent type hash follows the scheme:

| Scheme (tag) | Device type | Grantee type |
|---|---|---|
| `evm_eip712` | `EvmDevice(string scheme,address wallet,bytes32 privacySalt)` | `EvmGrantee(string scheme,address wallet,bytes32 privacySalt,string siteLabel,uint8 slot)` |
| `sol_ed25519` | `SolanaDevice(string scheme,bytes32 publicKey,bytes32 privacySalt)` | `SolanaGrantee(string scheme,bytes32 publicKey,bytes32 privacySalt,string siteLabel,uint8 slot)` |
| `jubjub` | `JubjubDevice(string scheme,bytes32 x,bytes32 y)` | `JubjubGrantee(string scheme,bytes32 x,bytes32 y,bytes32 siteLabelHash,uint8 slot)` |
| `k256` | `K256Device(string scheme,bytes32 x,bytes32 y,uint8 envelope)` | `K256Grantee(string scheme,bytes32 x,bytes32 y,uint8 envelope,bytes32 siteLabelHash,uint8 slot)` |
| `p256` | `PasskeyDevice(string scheme,bytes32 x,bytes32 y,string origin,bytes32 passkeyRpHash)` | `PasskeyGrantee(string scheme,bytes32 x,bytes32 y,string origin,uint8 slot)` (its RP is the scope's `passkeyRpHash`) |

The circuit derives the target's entry or grant id from exactly these values, with the target scheme's own recipe (FR-005). An unregistered tag is refused (the S1 tightening).

**A Solana target is a point** (Q37). `add_device`, `remove_device`, `issue_grant` and `revoke_grant` take a `Curve25519Point` beside the descriptor (inline: compactc 0.35.0 cannot emit an exported struct that holds one). The circuit derives the key's 32-byte RFC 8032 encoding with the descriptor module's ed25519 class, which refuses the identity (`A ≠ O`; the point type admits only the prime-order subgroup), and shows that derived key as `publicKey`; the entry or grant id hashes the same key. A circuit computes every descriptor class, so for any other target the client passes a fixed non-identity point (the Ed25519 base point), whose results the circuit discards. The class costs about 16k rows per circuit (the encoding about 10.2k, the rest its own SHA-256 derivation).

The enumerated members are shown as text labels (Q35): EIP-712 `string` members whose text is a circuit constant selected by the value, so the label and the value cannot disagree; a value with no label is refused (client and runtime; a constraint of the proof). The texts are the base's shared labels (`WalletArmRendering.compact` `recipient_kind_text` and `k256_envelope_text`; the client's `src/wallet/labels.ts`), so every readable arm shows the same words. The circuit holds `keccak256(text)` for each, which is how EIP-712 encodes a `string` member, and the offline suite checks, for every value, that the base circuit's own text equals the client's label and the signed text, and that the contract's digest equals the codec's. Labels cost at most 28 rows (`issue_grant`) and change no circuit's k. Calling the base circuit in place of the constants would add a keccak256 of the text per label: 4,463 rows per label when the signed string is the base's 24-byte space-padded text (`issue_grant` 260,484 rows, 1,660 below the k 18 cap), and k 19 for `issue_grant` (289,799 rows) when it is the exact text, because each text length needs its own hash.

| Member | Value | Label | Meaning |
|---|---|---|---|
| `IssueGrant.recipientKind` | 0 | `any recipient` | no recipient pin |
| | 1 | `unshielded user address` | pinned to a user address (unshielded twin) |
| | 2 | `shielded coin public key` | pinned to a Zswap coin public key (shielded twin) |
| | 3 | `contract address` | pinned to a contract (direct-transfer twin) |
| `K256Device.envelope` | 0 | `SHA-256 of the challenge` | the key signs SHA-256 of the challenge |
| | 1 | `dApp-connector signData` | a **full-control device** that signs a 32-byte hash through a connector's `signData` prefix; its own user sees only an opaque hash. A client SHOULD warn before such a device is added |
| `K256Grantee.envelope` | 0 | `SHA-256 of the challenge` | as above |
| | 1 | `dApp-connector signData` | upstream admits it for read-only grants only (a spend under it is refused) |

The effect lines (FR-023, Q20) are circuit constants:

| Type | `effect` |
|---|---|
| `AddDevice` | Gives this key FULL control of this account |
| `IssueGrant` | Lets this key use this account within the limits below |
| `PublishRecoverySession` | Sets this account's recovery key |
| `RotateEncKey` | Sets the key that can read this account's private coin records |
| `RemoveUnknownDevice` | Removes a device this wallet cannot identify |

## 6. What is shown, and the four labelled values

Every member is a value shown in full: an identifier, a key, an amount, a counter, a witness value, a ciphertext as `bytes`, or circuit-fixed text. The offline suite classifies every member of every type, and fails on a member it cannot classify. Exactly four hash-like values appear, each under a fixed name, and none of them grants authority (FR-004; Q17, Q20, Q21):

| Member | Value | Why it cannot be a preimage |
|---|---|---|
| `siteLabelHash` (`JubjubGrantee`, `K256Grantee`) | a `jubjub`/`k256` grantee's `origin_hash` | upstream hashes a client id of any length; the client shows the client id beside it |
| `passkeyRpHash` (`PasskeyDevice`, `IssueGrant`) | a passkey's `rp_id_hash` | the RP ID may be a registrable parent of the origin's host; the client shows the RP ID beside it |
| `privacySalt` (`EvmDevice`, `SolanaDevice`, `EvmGrantee`, `SolanaGrantee`) | the target's blind | a secret by design (section 2) |
| `entry` (`RemoveUnknownDevice` only) | a literal device entry, under "Removes a device this wallet cannot identify" | revocation only; the caller's own post-roll entry can never be removed |

Ledger-pinned private openings are not shown: the signer's own blind and use counter, `scope_salt`, `spent_prev`, and the grantee's pinned recipient and maximum coin value. They are checked against state, not chosen. A shielded spend shows its coin by nonce, value and Merkle index. Its colour is `color`, because the circuit asserts `coin.color == color`. The change is `coinValue − amount`.

**Verifiable by eye** (FR-022):

- the EVM address (MetaMask shows `address` members in EIP-55 form);
- the passkey origin;
- the 32-byte Solana key (shown as hex, derived in-circuit from the target's point; the client shows the base58 form beside it).

**Shown only**: `k256`, `jubjub` and passkey public keys, and the recovery material of `PublishRecoverySession` (the new recovery key, the session identifier, the phi values and the wrap). The material comes from the client's own guardian ceremony; that it is the intended guardians' is a client obligation, not something the user can check by eye (the Q18 residual, section 12).

**Length bound per layout**:

- every struct is fixed at its member count;
- the dynamic members are `entry` and `changeEntry` (192 bytes) and `wrap` (64 bytes);
- the longest message is `IssueGrant`: 22 words plus a 6-word grantee struct (7 words for `K256Grantee`).

## 7. Client codec

`src/wallet/evm-eip712-codec.ts` has two parts:

- a general EIP-712 encoder written from the EIP;
- one builder per operation, producing `eth_signTypedData_v4` JSON. The `types` object holds only the primary type, its nested type and `EIP712Domain`, because viem and ethers refuse unused types.

The builders are strict. They range-check every integer, check labels and origins against the circuit's text rules, and refuse an unregistered tag. These are client-layer refusals, before any wallet sees the message.

## 8. Frozen vectors

`src/tests/vectors/evm-eip712-v1.json` holds:

- **53 positive vectors.** Every primary type is covered, and every descriptor-taking type with all five schemes. The vectors include edge values (`2^128 − 1`, `2^64 − 1`, zeros), dynamic members with leading zero bytes and all-zero bytes, and the passkey parent-domain shape. Each vector holds its inputs, its typed data, the `encodeType` string, the domain separator, the struct hash and the digest. **viem's `hashTypedData` computed every hash.**
- **16 negative vectors.** Each names the layers that must refuse it:

| Negative | Refused by |
|---|---|
| an unregistered device tag; a space-padded registered tag; a grant-id tag as a device tag | client, runtime |
| a passkey origin with a space or a NUL | client, runtime |
| a site label ending in a space, with a double space, or empty | client, runtime |
| an unregistered grant-id tag | client, runtime |
| an amount above the spent coin (device and grantee) | client, runtime |
| an amount of 2^128; an `authNonce` of 2^64; a 191-byte inbox entry | client, runtime |
| a `recipientKind` of 4; a k256 `envelope` of 2 (no label) | client, runtime |

"Runtime" is the generated JavaScript of the contract's pure circuits. In the impure circuits the same asserts are constraints of the proof: the constraint-level refusals are recorded per circuit (`evm-eip712-prover.ts`).

Agreement, from `npm run test:evm_eip712-offline`: the contract's pure circuits, the client codec and the frozen values agree on all 53 vectors. To reproduce the frozen values with viem, which is not a dependency (Q24):

```sh
VIEM_DIR=<a viem 2.x package root> npx tsx src/tests/evm-eip712-viem.ts
```

That script also checks that `signTypedData` is byte-identical to viem's, and the addresses, points and blind requests.

## 9. The seam and the acceptance policy

`require_authorised_with_evm_eip712<T>(auth, type_hash, tail)` follows upstream `p256`'s order (FR-007):

1. the device's address derived from the presented point, `evm_eip712_address(auth.pk)` (the point at infinity refused in both encodings);
2. membership of the single-use entry at the active epoch;
3. `r ≠ 0` and `s ≠ 0`;
4. ECDSA verification of `digest(account, struct_hash)`, where the seam builds `struct_hash` itself from the frame and the export's tail;
5. the entry rolled to its successor;
6. `auth_nonce` advanced and `round` bumped.

Any failure aborts the whole call. The trailing argument `EvmEip712Auth { pk, use_counter, blind, sig }` is internal.

There are three entry points, and one internal core that only they call: `require_authorised_with_evm_eip712<T>` (one message type), `require_authorised_with_evm_eip712_either<T, U>` (`remove_device`'s two forms: it builds both struct hashes from its own frame and verifies the one the call selects) and `require_authorised_with_evm_eip712_bare` (a type with no members of its own, `RevokeAllGrants` and `CancelRecovery`). Each derives the address and builds its frame, then hands the address and the struct hash to `evm_eip712_verify_and_roll`. Each returns the caller's post-roll entry, which `remove_device`'s S13 guard needs.

**The grant seam** (`require_grant_with_evm_eip712<T>`, grantee role) applies the same rule to the grantee frame (`account`, `grantee`, `siteLabel`, `slot`, `issuedAt`, `grantNonce`). It derives the grantee's address from the presented point, then the grant id from that address, the blind, H(origin tag ‖ label) and the slot. It reads `issuedAt` and the nonce from the record, never `auth_nonce`, and touches no device entry (FR-008). The MIP's steps run in order: the record by id; liveness (active, epoch, generation, expiry); upstream's shared `check_spend_scope` (operation, caller pin, object, per-call cap, spent opening, cumulative cap, recipient pin); `r ≠ 0`, `s ≠ 0`; the signature; the record written back with its nonce advanced and the new spent commitment; `round` bumped. The shielded twins assert `coin.color == color` and run upstream's `check_shielded_grant_bounds` (coin value, live `enc_key`) first.

**The arm's own rules on top of upstream's chips.**

- Every shielded spend asserts `coin.color == color` (FR-010) and `amount ≤ coin.value`.
- `add_device` derives the new entry at the current `device_epoch` and counter 0, so the arm cannot plant a future-epoch entry.
- `remove_device` takes the target's epoch and counter (removal only reduces authority, so a planted `device_epoch + 1` entry can be evicted), or a literal entry under the Q20 line. The Maybe that selects the form must be canonical when absent.
- `issue_grant` hashes the read key as zero, and requires it to be zero, when `read` is off (audit G1E-7). It requires a non-zero key when `read` is on. It admits an RP hash only for a passkey grantee, so that no other hash-like value ever appears in an approval. It stores SHA-256 of the shown read key as `read_pk_hash`, as the grants MIP defines it.

**The seam owns the frame** (audit G1E-1, G0 C9). An export passes only its operation's type hash and tail, from the module's `evm_eip712_parts_<operation>` circuit. The seam supplies every frame value itself: `account` is `kernel.self()`, `device` is the address of the presented point, and `authNonce` is the ledger's (read before this call advances it). No export can name an account, a device or a nonce, so an entry is matched and a signature verified only for the address of the key that signed. The exported struct-hash oracles `evm_eip712_struct_<operation>` are built from the same frame builders (`evm_eip712_device_struct<T>`, `evm_eip712_grantee_struct<T>`) and the same parts, so an oracle and its export cannot diverge. `keccak256` over a tuple whose last member is a generic tuple hashes that member flat (QA-A1; the contract, the client and the independent implementation agree on every frozen vector), and the refactor cost no rows. A malicious-prover mutant that forges the derived address in the generated JavaScript (so that the victim's entry matches while the attacker's key signs) is refused at the proof server (`evm-eip712-prover.ts`, section `frame`).

The table below gives the acceptance policy. Each rule's refusing layer was measured with the JavaScript checks bypassed, after a proved positive control (`npm run test:evm_eip712`, `evm-eip712-prover.ts`). On the final build (2026/10/15) the suite ran 241 cases across all 16 circuits: 126 refused at layer `constraint`, 61 at `constraint on a declared read`, 3 decoding refusals, 5 runtime-only (the reason recorded), 37 positives proved, 8 state-only positives and 1 case not applicable (reason recorded), with 77 positive controls proved through each negative's own patched copy ([evidence](evidence/evm-eip712/prover-suite.json)).

| Rule | Enforced by | Refused at (simulator / prover) |
|---|---|---|
| The signature covers exactly the executed values (binding: `newKey`, `account`, `device`, `authNonce`, `effect`, the domain's name, version and verifyingContract, the type name, a member name) | the in-circuit digest + `secp256k1EcdsaVerify` | "invalid signature" / `/check` 400 "Failed direct assertion" |
| The key, blind and counter open a live entry (an unenrolled key, another blind, a wrong counter) | the entry membership assert | "unknown device entry" / `/check` 400 |
| `r ≠ 0`, `s ≠ 0`, and `(r, s) = (0, 0)` | the arm's zero-scalar assert (and ZKIR's inverse) | the arm's assert / `/check` 400. `(0, 0)` verifies in the generated JavaScript once inverses of 0 are taken as 0, so only the arm's assert fires there, and the proof still fails |
| Both S forms accepted | `secp256k1EcdsaVerify` (FIPS 186-5) | the high-S twin proves and lands. The low-S original is then refused: "unknown device entry" (simulator), `/check` 400 (prover), and node `1010: Invalid Transaction: Custom error 104` for its proof made before the twin landed (three submissions; a fresh call from the same wallet landed in between) |
| The point at infinity (flagged) | ZKIR coordinate extraction; the arm's coordinate guard and the stdlib's struct guard (defence in depth) | "cannot extract the x-coordinate" / "Cannot extract coordinates of the Secp256k1 identity" |
| The unflagged `(0, 0)` | the runtime validator; the honest proof server's input decoding; in-circuit, the `Secp256k1Point` on-curve assignment (`(0, 0)` is not on the curve) | type error / proof-server input decoding "Failed to decode" (a decoding refusal of an honest prover, not a constraint failure; see the note below) |
| A coordinate not reduced below `p` (QA-1) | the runtime's foreign-field encoder; the honest proof server's input decoding; for soundness, the size argument below | type error / proof-server input decoding "The encoded value of type Secp256k1Point is not in canonical form" (not a constraint failure) |
| Replay across accounts, arms (`k256` ↔ `evm_eip712` with the same key), operations (`CancelRecovery`, `RevokeAllGrants`), roles (a grantee type) and nonces | the domain and type hash in the digest; the arm-specific digest rule | "invalid signature" (or "unknown device entry" for a consumed entry) / `/check` 400 |

**Decoding refusals are not constraint refusals** (audit G1E-4). The last two rows above are refused by the honest toolchain: the runtime's encoder and the proof server's input decoder. A malicious prover builds its own witness and never runs that decoder, so these rows do not show that a constraint refuses the value. The closure for this arm is a size argument. A secp256k1 coordinate `c` has a second 32-byte representation `c + p` only when `c < 2^256 − p ≈ 2^32`. For any real key the cast to `Bytes<32>` therefore has no alternative output, and forging an address through it would also need a keccak256 preimage. The same bound applies to the `secp256k1PointX` inside `secp256k1EcdsaVerify`. The `(0, 0)` point is refused in-circuit by the on-curve assignment. Constraint-level canonicity of the foreign-field-to-bytes cast itself remains an upstream residual (#182).

**Predicates over ledger reads hold through the constraint and the node's replay together** (audit G2E-4). Many asserts test a value the circuit reads from the ledger or the call context: the entry's membership in `devices`, the grant record (its liveness, caps, commitments and nonce), `enc_key`, `auth_nonce`, the mirror balance, the block time, the caller. Such a read enters the proof as a public transcript value that the prover declares. An honest prover declares the real value, and the assert fails at the proof server. A malicious prover can declare the value the assert needs and prove the call; the node then refuses the transaction, because it re-runs the transcript against the real state. The evidence labels these refusals `constraint on a declared read` (as distinct from `constraint`, a relation over the call's own inputs and witnesses, such as every signature-binding case). The node-side half is shown by the stale-proof run of section 9's table: a proof made against an earlier state was refused by the node (`1010` / 104), and replaying its transcript with the ledger's own `QueryContext.runTranscript` reports `mismatch between expected … and actual … read` for the `auth_nonce` read.

**The grantee path** (`require_grant_with_evm_eip712` and the three twins), measured the same way (`evm-eip712-prover.ts` sections `grants`, `grant-matrix`, `frame-lifecycle`; every case under a valid grantee approval, with the honest call proved through the same patched copy first):

| Rule | Enforced by | Refused at (simulator / prover) |
|---|---|---|
| The approval covers exactly the executed values (amount, recipient, colour; for the shielded twins the change entry, the encryption key and the spent coin's nonce, value and Merkle index) | the in-circuit digest + `secp256k1EcdsaVerify` | "invalid grant signature" / `/check` 400, constraint |
| The record is live: active, of the current device epoch and grant generation, not expired | the grant seam's four asserts | "grant revoked", "grant epoch stale" (after a recovery finalisation, which keeps `grants`), "grant expired" / `/check` 400, a declared read. "grant generation stale" is **unreachable** in this contract: `revoke_all_grants` bumps the generation and clears the map, and no chip writes a record of another generation; it is defence in depth for a ledger that keeps records, exercised on a state built by copying the generation cell |
| The scope: per-call cap, cumulative cap, recipient pin, caller pin (no contract caller; another contract), object, spent opening | upstream's shared `check_spend_scope` | the chip's messages / `/check` 400, a declared read (the record and the caller are reads) |
| A coin above the grant's max coin value; a change sealed to a key that is no longer live | upstream's shared `check_shielded_grant_bounds` | "coin above max_coin_value", "stale encryption key" / `/check` 400, a declared read |
| The spent coin's colour is the approved colour (FR-010) | the twin's own assert | "held coin colour does not match the withdrawn colour" / `/check` 400, constraint |
| `r ≠ 0`, `s ≠ 0` | the grant seam | the arm's assert / `/check` 400, constraint |
| The grantee address is derived from the presented point (a forged derivation) | the grant seam | "unknown grant" / `/check` 400 "Public transcript input mismatch" |

The grant call never reads or advances `auth_nonce` or a device entry (FR-008). That rests on the source (the grant seam reads `issued_at` and the nonce from the record and writes back only that record and `round`) and on state checks in the simulator and on node; unchanged state alone cannot show that a value was not read, so it is not counted as a constraint-level result.

**Field values are rendered canonically** (G1S-6, QA-S3). `PublishRecoverySession` shows the JubJub recovery key's coordinates and the phi values as 32-byte little-endian words, cast in-circuit from `Field` to `Bytes<32>`. ZKIR 3.1 lowers the cast to `div_mod_power_of_two(val, 248)`, which decomposes the value with `assigned_to_le_bits(val, None, enforce_canonical = true)` over all 255 bits (midnight-circuits 7.2.4: the low bit is tied to `sgn0(val)`, which leaves exactly one bit vector). A value `f` therefore has one rendering, never `f + r`. The prover suite (section `qa-s3`) signs each of the four members over its non-canonical rendering `f + r` and executes `f`: each of the four is refused at the proof server (`/check` 400, layer `constraint`), after the canonical rendering proved through the same patched copy.

## 10. Network (Q4, FR-015)

The domain carries no network value, as upstream's arms carry none: the contract has no network field, and a circuit cannot read the network id (Compact's `Kernel` offers no such read). What binds an approval is the account: the domain's `verifyingContract` is derived from the account's address, the frame names the account, and the device entry is derived from the account address and the blind.

**The clone argument** (audit C3). The ledger derives a contract's address from its deploy (initial state and nonce) alone, without the network id, and signs maintenance updates over `(address, updates, counter)`. Someone who replays an account's public deploy on another network therefore gets an account at the same address, with the same initial state. Whenever that clone is in the state an approval was signed against (the same device entry and `auth_nonce`), the approval verifies there as well, because nothing in it names the network. No in-contract value can tell the clone apart: a salt sealed into the state at deploy time is copied with the deploy, and the network id cannot be read. So the arm does not claim network separation, and the MIP's "SHOULD bind a network" is replaced by this argument.

**Mitigations.**
- The reference client deploys with a fresh random deploy nonce and a fresh 32-byte boot salt, so an honest account has no twin unless someone deliberately replays its deploy and its history on another network.
- The blind request names the network (section 2), so the same wallet has different blinds, and therefore different entries, on different networks.
- The upstream ledger issue proposing that the network id be bound to the contract address, to the maintenance-update envelope, or be exposed to circuits is drafted (filing pending).

## 11. Measurements

The per-circuit report (k, rows, prover-key size, proving time, verifier-key bytes) is [EVM-EIP712-MEASUREMENTS.md](EVM-EIP712-MEASUREMENTS.md), with its evidence in [evidence/evm-eip712/circuit-sizes.json](evidence/evm-eip712/circuit-sizes.json). Every circuit is at k ≤ 18; the widest is `issue_grant_with_evm_eip712`.

Where the rows go (mock-compile measurements of the layouts, before the byte formats were frozen):

- keccak256 costs about 4.2k rows per 136-byte block. A tuple of `Bytes<32>` words hashes at that cost; building one flat `Bytes<N>` from slices costs about 18k rows more per 128 bytes, so every preimage here is a tuple.
- The domain separator costs about 14.8k rows per call. It cannot be cached: a cache would need a ledger or constructor field (FR-001).
- `secp256k1EthereumAddress` costs about 31.5k rows (mostly its byte reversal), ECDSA verification about 40.4k.
- A big-endian `uint128` word costs about 4.7k rows and a `uint64` about 2.3k; addresses, booleans and `uint8` words are free as tuple elements.
- Reversing a `Bytes<32>` costs little when the bytes are inputs (the k256 and P-256 descriptor coordinates) and about 4k rows when they come from a cast inside the circuit. Q29 therefore keeps JubJub coordinates and `Field` values little-endian: showing the recovery lines big-endian would add 24,407 rows and move `publish_recovery_session_with_evm_eip712` from k 17 to k 18.
- The blind costs one SHA-256 block (about 1.9k rows) per derived entry or grant id.
- The enumerated-member labels (Q35) cost at most 28 rows.

## 12. Recovery

Two device-gated circuits use upstream's shared recovery chips through the seam:

- `publish_recovery_session_with_evm_eip712(new_recovery_pk, session_nonce, phi_1, phi_2, phi_3, phi_4, phi_len, wrap, auth)` runs `do_publish_recovery_session`;
- `recover_cancel_with_evm_eip712(auth)` runs `do_recover_cancel`.

The recovery gate (`recover_submit`) and finalisation (`recover_finalise`) have no arm. The gate is opened by the recovery secret and the successor's co-signature, and finalisation is permissionless after the veto window.

**What the session approval shows** (FR-004, FR-023). `PublishRecoverySession` carries the fixed line "Sets this account's recovery key". It also carries every operand in full:

- the new recovery key's JubJub coordinates (`recoveryKeyX`, `recoveryKeyY`);
- the four phi values (`phi1`…`phi4`; unused slots are shown as zero);
- the session identifier, `phiLength`, and the 64-byte `wrap` as `bytes`.

Coordinates and phi values are 32 bytes little-endian each, as the contract encodes them (Q29). The circuit recomputes the digest from exactly the values it then stores. The test `evm-eip712-recovery-sim.ts` checks that the stored recovery key, session identifier, phi values and wrap equal the shown ones. `CancelRecovery` is the bare frame (`account`, `device`, `authNonce`). Its type hash keeps it apart from `RevokeAllGrants`, which has the same members.

**The shared chip's rules apply as on every arm**, under a valid signature:

- no session while a recovery is pending;
- a phi length of 1 to 4, with unused slots zero;
- a non-zero, fresh session identifier;
- a fresh recovery commitment that is not the identity and not of small order;
- nothing to cancel is refused.

The client facade (`evmEip712RecoverySession`) refuses the same values before the wallet is asked to sign.

**Finalisation retires every `evm_eip712` device** (upstream #183). `recover_finalise` clears the device set before it installs the successor's entry. Every old entry is gone afterwards, including an `evm_eip712` entry that an upstream arm's raw `add_device` planted at `device_epoch + 1` before the recovery (README erratum 7). That plant equals the planted device's entry at the new epoch and counter 0, so the bump alone would have left it live. After finalisation it is refused together with every other old device: in the simulator, at the proof server (with the generated JavaScript's checks bypassed), and on the shared stack against the finalised account's state (refused before submission by the generated JavaScript). This arm's own `add_device` cannot plant such an entry (section 9).

## 13. Direct transfers (Q34)

`withdraw_shielded_to_contract_with_evm_eip712` and its grantee twin send a shielded coin to another contract, which must claim it in the same transaction with its own `deposit_shielded` (MIP-0012 §6.6). Two client-side facts govern how such a transaction is built today:

- midnight-js 5.0.0-rc.2 (upstream's pin) refuses to build the sender's call alone: `assertReceivesMatchClaims` requires every contract-addressed output to be claimed inside the same call tree. The arm's tests build it with a test-only copy of the builder that drops that pre-check (`relaxedContractsModule` in `src/tests/evm-eip712-negative.ts`); the node still checks the claim.
- The ledger matches a claimed output to its receive by segment, commitment and recipient. A claim grafted on as another intent is refused (`Custom error: 218`). What lands is both calls in one intent, with the recipient's call moved into the fallible segment when the sender's claim is partitioned fallible (the partitioner splits each call's transcript into guaranteed and fallible halves on its own).

**The effect of a failed fallible half.** The seam's state change (the device entry rolled, `auth_nonce` advanced) and the transfer can sit in different segments. If the transfer's fallible segment fails, the guaranteed segment still applies: the approval is consumed, the fees are paid, and no coin moves. The device must sign a fresh approval (over the new `auth_nonce`) to try again. A client should present a failed direct transfer as "not sent; approve again", never as pending.

## 14. Privacy and provenance

**What the blinding gives** (FR-013). The ledger holds, for each `evm_eip712` device, only SHA-256 outputs over its address and its blind: the boot commitment, the entries and the grant ids. Without the blind, a known Ethereum address cannot be tested against them. The point, the address, the blind and the signature are private inputs of every proof; the disclosure review of every `disclose` in the arm and its codec finds no other path, and a needle scan of every transaction and contract state of the arm's localnet runs found none of them in the clear.

**What it does not give.**
- The blind is derived from a signature, so whoever obtains that `personal_sign` signature (for example a phishing page that shows the request) learns the blind and can recognise the account's entries. That is a loss of privacy, not of control: the blind authorises nothing.
- A grantee's blind is shown to the issuer (`EvmGrantee.privacySalt`), who needs it to derive the grant id. The client therefore derives a grantee's blind from its own request (`granteeBlindMessage`: "Midnight Passport grantee privacy key", the role, the network, the wallet and the issuing account's address, no account index; Q39), so the issuer never learns a device blind, and every issuer gets a different blind. The issuer can still recognise the grantee's calls on the issuer's own account, which is what a grant is for.
- A non-deterministic signer (MPC, hedged nonces) cannot re-derive its blind; enrolment signs twice and refuses it.

**Provenance** (FR-023, Q18). The wallet shows every key and every piece of recovery material in full, but showing a key does not prove whose it is. A user who approves `AddDevice`, `IssueGrant` or `PublishRecoverySession` with a key or recovery material supplied by an attacker gives the attacker what the circuit-fixed effect line says. The mitigations:
- the effect lines are circuit constants ("Gives this key FULL control of this account", "Lets this key use this account within the limits below", "Sets this account's recovery key", "Sets the key that can read this account's private coin records"), so a page cannot soften them;
- the new device's own client renders the identical descriptor, so the user can compare the two screens (MIP-0013 S7); for an EVM device the address, and for a Solana device its 32-byte key, are forms the user can check against the other wallet by eye (section 6);
- recovery material comes from the client's own guardian ceremony, never from a page (a client obligation).

What remains is documented, not closed: a key the user cannot check by eye (`k256`, `jubjub`, a passkey's public key) is trusted on the strength of the client that shows it.
