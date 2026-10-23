# Scoped-grant validation — 2026-10-23

This record accompanies the Passport review of the
[scoped-grants Draft](../docs/mps-mip/mips/mip-xxxx-scoped-grants.md).
It distinguishes executable-contract evidence from the broader connection
ceremony and adoption requirements. It does not declare the MIP Active.

## Implementation

The account already implements schema v3 with JubJub, k256 and profiled
P-256 grant arms. This change adds a client capability check: both grant
issuance entrypoints refuse `spec_version < 3` (or a missing version),
before the high-level method requests a device signature or the low-level
method submits. A v2 scope does not contain the caller commitment and
cannot consume the v3 digest, including for an unrestricted grant.

No Compact cryptographic check was added. Raphael's
[PR #182](https://github.com/midnightntwrk/passport/pull/182), at
[`1932fab4`](https://github.com/midnightntwrk/passport/tree/1932fab4c422e301706d422648d558277e00af64),
already records the zero/out-of-range scalar and malformed-key checks for
secp256k1 and P-256. Its runtime/native-validation evidence must not be
described as a complete adversarial ECDSA proof audit.

## Reproduction and provenance

The base is Passport `3fa1b32585032305f3dbef15476dd5fe7fca8a4b`.
Compact 0.35.0 (commit `debb05f9414b9d1e176741c2be289bb32233f0fc`),
language 0.27.0 and runtime 0.20.0 were used with the repository lockfile.
The node, indexer and proof-server versions are recorded in each node
evidence JSON and match `infra/docker-compose.yml`.

The unchanged account source was freshly compiled with `--feature-zkir-v3
--skip-zk`. All 52 textual ZKIR files matched existing compiled artifacts
byte for byte. Matching binary ZKIR and cached proving/verifier keys were
used, with SHA-256 entries in the local compiler manifest. The artifact
integrity checks remained enabled. `test:toolchain-offline` loaded every
circuit and checked the ten-wave deployment plan for all three owner
arms. Node evidence includes the source/runtime and exercised artifact
hashes; proving keys and generated code are not committed.

For a clean checkout, generate the artifacts with `npm run compile`,
then run these commands from `contract/`:

```sh
npm run build
npm run test:unit
npm run test:toolchain-offline
npm run test:grants-offline
npm run test:grants-capability-offline
npm run test:grants-caller-offline
npm run test:p256-offline
npm run test:recovery-sim
cargo build --locked --manifest-path signer-rs/Cargo.toml
npm run test:crossimpl-offline
```

All of these checks passed. The grants suite reports 127 passing checks.
The cross-implementation suite uses the separately built Rust signer;
the capability suite uses a client fixture and does not replace a real
legacy-account installation control.

The expanded recovery simulator also checks both JubJub and k256 grantees
for independent slot revocation, refusal to overwrite an expired but
unrevoked record, and a cumulative wrap attempt after a legitimate
`2^128 - 2` spend. That last case supplies the correct committed running
total before attempting another 2 units; it reaches the cap check rather
than merely failing a commitment opening. Foreign-colour witnesses are
refused by both shielded twins on both arms. These boundary cases are
simulator evidence unless a node result below explicitly repeats them.

Start the repository's localnet, configure its documented development
funding wallet, and run node suites sequentially to avoid funding-wallet
races. Set `EVIDENCE_DIR` to a fresh directory to preserve historical
records:

```sh
npm run test:p256-grants
npm run test:p256-grant-refusals
npm run test:recovery
```

## P-256 grant spending on node

The [recorded run](evidence/grants-completion-20261023/p256-grants-conformance.json)
passed with a full 52-circuit account. An OpenSSL software authenticator
supplied the bounded `wa-json134` assertions. Eleven recorded funding and
lifecycle transactions succeeded, including three grantee spends of 5
units each; the funded balance went from 100 to 85.

All 16 negative controls passed against indexed chain state. They cover
origin and RP bindings, profile-invalid client data, modified signatures
and amounts, per-call/cumulative caps, token colour, recipient pin, replay,
revocation, the original nonce-zero signature against a fresh incarnation,
read-only scope and a root call to a caller-restricted grant. Each refusal
made zero prover and submission calls and left the complete serialised
contract state unchanged. These are build-time refusals, not submissions
of invalid proofs to the node.

The owner signature prepared before the first grant spend remained valid
afterwards. The source and artifact hashes captured before and after the
run matched. Browser ceremony and successful forwarded or shielded P-256
grant calls remain outside this run.

The separate [refusal fixture](evidence/grants-completion-20261023/p256-grant-refusals.json)
also passed. It installs the original constructor state and three original
operations with their verifier keys, with maintenance authority retired.
Three setup transactions deploy, activate an owner and issue a real P-256
grant. This restricted, unfunded fixture complements the full deployment;
it is not itself a complete account implementation.

The identity key fails native point validation, the ED flag fails the
fixed-profile policy, and a correctly signed 44-byte authenticator-data
envelope containing an ED flag and CBOR extension map fails the
`Bytes<37>` argument boundary. A valid ordinary assertion reaches the
expected unfunded custody guard. These distinct refusal layers are
recorded explicitly; every call leaves complete serialised state
unchanged without proving or submitting. The extended assertion's ES256
signature is independently verified before the control runs. This closes
the bounded-profile identity/extension evidence gap without adding a
cryptographic guard or rejecting extensions in other WebAuthn profiles.

## Recovery and grant lifecycle on node

The expanded [recovery run](evidence/grants-completion-20261023/rec-1-9-recovery-conformance.json)
passed on a fresh full account. For both JubJub and k256, revoking one
slot leaves another grant for the same key usable, without changing
device authority. An expired but unrevoked grant cannot be overwritten.
This does not claim the separate expired-record revoke-plus-issue
composition case in one transaction.

The suite publishes a recovery session, reconstructs its secret from
guardian shares, opens its on-chain wrap, checks early-finalisation
refusal, cancels, and resubmits. A JubJub grant issued before recovery and
a k256 grant issued while recovery is pending both become unusable after
finalisation. They remain unusable after a second recovery; each epoch
retains exactly its authorised successor device.

The final successor revokes and reissues both grant ids. Old-incarnation
signatures fail even with the fresh scope opening and matching nonce
zero. Fresh signatures spend successfully through both grantee arms,
advancing the grant state and round while preserving device entries,
device count and authorisation nonce. Negative cases compare the
explicitly tracked state fields recorded in the JSON, not a complete
contract-state or UTXO snapshot. Source/runtime and exercised circuit
hashes identify the run.

The recovery JSON's byte objects are formatted inline for review; its
parsed data is identical to the original harness output. All 70 captured
source/runtime and artifact hash entries across the three node records
were checked against the final working tree. The isolated Compose project
`passport-scoped-grants-review` was stopped after the runs; its data
volumes were retained.

## Remaining MIP work

The complete authoriser/dApp connection ceremony, browser attack matrix,
GrantViewSeal handover and re-sealing, non-browser connection forms,
independent implementation and cryptographic review remain separate
acceptance work. The node additions here use non-native unshielded assets;
they establish neither a P-256 shielded grant spend nor a successful
forwarded P-256 call. The wider rejection matrix and pre-grants
installation control retain their explicit status in the Draft.

The Draft defines its combined conformance with MIP-0013 directly.
Passport review is the first submission; publication or adoption in the
canonical MIP repository is a subsequent step.
