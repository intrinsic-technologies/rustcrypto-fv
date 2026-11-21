# rustcrypto-fv

Lean specifications of ten [RustCrypto](https://github.com/RustCrypto) crates, and 71 theorems
stating that the crates' compiled x86-64 code, run on lean-x86's machine model, computes those
specifications.

## Verified crates

The theorems cover the operations below. Each crate's `comparator.config.json` lists its theorems
under `theorem_names`, and [comparator](https://github.com/leanprover/comparator) checks every
theorem listed.

| Crate | Operations | Theorems |
| --- | --- | ---: |
| [md-5](Md5/) 0.11.0 | `Md5::digest`; `new`, `update`, `finalize`; the `reset`, `finalize_into` and `compress` variants | 10 |
| [base16ct](Base16ct/) 1.0.0 | `lower::encode`, `upper::encode` and their `_str` forms; `lower`, `upper`, `mixed::decode`; `encoded_len`, `decoded_len` | 9 |
| [sha1](Sha1/) 0.11.0 | `Sha1::digest`; `new`, `update`, `finalize` | 2 |
| [sha2](Sha2/) 0.11.1 | `digest`; `new`, `update`, `finalize`: each of SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 | 12 |
| [sha3](Sha3/) 0.12.0 | `digest`; `new`, `update`, `finalize`: each of SHA3-224, SHA3-256, SHA3-384, SHA3-512, Keccak-224, Keccak-256, Keccak-384 and Keccak-512 | 16 |
| [aes-gcm](AesGcm/) 0.11.1 | `Aes128Gcm` and `Aes256Gcm`: `new`, `encrypt_in_place`, `decrypt_in_place` | 4 |
| [chacha20poly1305](ChaCha20Poly1305/) 0.11.0 | `ChaCha20Poly1305::new`; `encrypt`, `decrypt`, `encrypt_in_place`, `decrypt_in_place` | 4 |
| [p256](P256/) 0.14.0 | `SigningKey::generate_from_rng`, `try_sign`, `PublicKey::from_sec1_bytes`, `VerifyingKey::verify`, `Signature::from_slice`, `ecdh::diffie_hellman` | 6 |
| [k256](K256/) 0.14.0 | `SigningKey::generate_from_rng`, `try_sign`, `PublicKey::from_sec1_bytes`, `VerifyingKey::verify`, `Signature::from_slice`, `ecdh::diffie_hellman` | 6 |
| [hkdf](Hkdf/) 0.13.0 | `Hkdf::<Sha256>::new` with `expand`; `HkdfExtract::<Sha256>`: `new`, `input_ikm`, `finalize` | 2 |

Each crate's `Statements.lean` opens with a table giving, for each operation, its theorem, the
specification the theorem uses and the standard behind it. Each theorem's docstring says in prose
what it states. The crate's `README.md` explains how to read the theorem statements, any
deliberate differences from the standards, and how to build the verified binary.

## Repository structure

```text
Standards/                # Lean definitions of published standards, by publisher and subject
├── NIST/  SECG/  RFC/
├── Tests.lean            # `lake test -- Standards`; a subject's tests are in its Tests.lean,
│                         # which names the vector files it reads
└── README.md             # coverage table and original documents
Sha2/                     # one directory per crate, named like its Lean library
├── Spec/                 # specification, extracted program, call semantics
│   └── Program/Extracted/
├── Proofs/
├── Tests/Vectors/
├── program/              # Rust wrapper, pinned toolchain, extraction.toml
├── Spec.lean  Statements.lean  Proofs.lean  Tests.lean  TestDriver.lean
├── lakefile.lean  lake-manifest.json  lean-toolchain
├── comparator.config.json
└── README.md             # verified operations, theorem statements, differences, build
ci/                       # comparator, extraction, crate selection, convention and import checks
scripts/                  # extraction, local comparator
.github/workflows/        # Checks, Build, Tests, Extraction, Comparator; Select crates (shared)
lakefile.lean  Tests.lean  lean-toolchain  lake-manifest.json
```

Each crate is one Lean library with four root modules:

| Module | Role |
| --- | --- |
| `<Crate>.Spec` | Imports every specification module: the crate's specification, the extracted program, and the call semantics of its entry points |
| `<Crate>.Statements` | The comparator challenge: the crate's theorems, each with a `sorry` proof. It imports only specification modules |
| `<Crate>.Proofs` | The comparator solution: imports the proof modules, which restate and prove each theorem under the same name without importing `<Crate>.Statements` |
| `<Crate>.Tests` | Executable checks of the specification against published vectors (`run : IO Unit`) |

The [`Standards`](Standards/README.md) library holds the Lean definitions of published standards
that crates share, and it never imports a crate. The only permitted axioms are `propext`,
`Quot.sound` and `Classical.choice`.

Each crate is also its own Lake package. Its libraries read their sources, including `Standards`,
from the repository root. Each crate pins its versions of Lean, lean-x86 and lean-x86-proofs, and
its `program/` directory pins the Rust toolchain and crate version. The repository's own Lake
package builds and tests `Standards`.

## Extraction

```sh
python3 scripts/extract.py Sha2    # regenerate Sha2/Spec/Program/Extracted/
bash ci/check-extraction.sh Sha2   # regenerate and compare with the checked-in files
```

[`scripts/extract.py`](scripts/extract.py) builds the crate's `program/` wrapper as a static library
for `x86_64-unknown-none` at x86-64-v1, and links it into a fixed image with
[`scripts/layout.ld`](scripts/layout.ld), or with the crate's own `program/layout.ld` where it has
one. It then runs lean-x86's `x86-extract` on the image and checks the extracted bytes against
`objcopy`. Source paths are remapped, so the output does not depend on where the repository is
checked out.

Extraction needs Rust (through rustup), Python 3, binutils, Make and a C compiler, as well as Lean
and Git. Intermediate files go in `.cache/`.

## Build and check

Install Lean through [elan](https://github.com/leanprover/elan). Lake fetches lean-x86 and
lean-x86-proofs over SSH (`git@github.com:intrinsic-technologies/…`), so a GitHub SSH key with read access
to both repositories is required.

To build and test `Standards`, run these from the repository root:

```sh
lake build Standards                   # the shared standard definitions
lake test                              # every Standards subject
lake test -- Standards.NIST.SHA2       # one Standards subject
```

Run a crate's commands from the crate's directory. Building checks the specification, statements
and proofs with the Lean kernel, and testing runs the specification against published vectors. For
example, for `Sha3`:

```sh
cd Sha3
lake build Sha3.Statements   # the theorem statements and the specification they use
lake build Sha3.Proofs       # the proofs
lake build Sha3              # everything: specification, statements, proofs and tests
lake test                    # the specification against published vectors
```

The same commands work for every crate: replace `Sha3` with `Md5`, `Base16ct`, `Sha1`, `Sha2`,
`AesGcm`, `ChaCha20Poly1305`, `P256`, `K256` or `Hkdf`. Each statement has a `sorry` proof by
design; `Statements.lean` sets `warn.sorry false`, so building the statements prints no `sorry`
warnings.

Comparator then checks that each listed theorem is proved with exactly its statement in
`Statements.lean`, using only the permitted axioms. To run it locally on one crate, without a
sandbox, from the repository root:

```sh
scripts/comparator-local.sh Sha3
```

The authoritative check is the Comparator workflow in CI, which runs two jobs:

1. **Challenge:** copies the `Statements` module and every module it imports, directly or
   indirectly, out of the checkout, and fails if one of them is a proof or test module. It then
   deletes the checkout, including the proofs and Git history, and builds the statements in a new
   sandboxed process.
2. **Verification:** rebuilds the statements in a fresh checkout, checks that the result matches
   the challenge's build, and runs comparator to check each listed theorem's statement, axioms and
   kernel validity.
