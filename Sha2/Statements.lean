import Sha2.Spec

set_option warn.sorry false

/-!
# sha2 0.11.1

Theorems about the compiled machine code of sha2 0.11.1: for each of the six hashers, one for the
one-shot `Digest::digest` and one for the sequence `Digest::new`, `update` once per part,
`finalize`. Each says that a well-formed call returns and writes the digest that the FIPS 180-4
function in `Standards/NIST/SHA2/` computes, with no crate specification in between.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Sha224::digest`; `Sha224::new`, `update`, `finalize` | `sha224_digest_writes_sha224_of_data`; `sha224_digest_slices_writes_sha224_of_message` | `SHA224` | FIPS 180-4 §6.3 |
| `Sha256::digest`; `Sha256::new`, `update`, `finalize` | `sha256_digest_writes_sha256_of_data`; `sha256_digest_slices_writes_sha256_of_message` | `SHA256` | FIPS 180-4 §6.2 |
| `Sha384::digest`; `Sha384::new`, `update`, `finalize` | `sha384_digest_writes_sha384_of_data`; `sha384_digest_slices_writes_sha384_of_message` | `SHA384` | FIPS 180-4 §6.5 |
| `Sha512::digest`; `Sha512::new`, `update`, `finalize` | `sha512_digest_writes_sha512_of_data`; `sha512_digest_slices_writes_sha512_of_message` | `SHA512` | FIPS 180-4 §6.4 |
| `Sha512_224::digest`; `Sha512_224::new`, `update`, `finalize` | `sha512_224_digest_writes_sha512_224_of_data`; `sha512_224_digest_slices_writes_sha512_224_of_message` | `SHA512_224` | FIPS 180-4 §6.6 |
| `Sha512_256::digest`; `Sha512_256::new`, `update`, `finalize` | `sha512_256_digest_writes_sha512_256_of_data`; `sha512_256_digest_slices_writes_sha512_256_of_message` | `SHA512_256` | FIPS 180-4 §6.7 |

Each theorem docstring below names the theorem's call predicate; every theorem also assumes the
machine conditions `hMachine` and `hBindings`, which the README describes.

How to read the theorem statements and how to build the verified binary are in `Sha2/README.md`.
-/

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

/--
`Digest::digest` for `Sha224` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message in
one call.

The wrapper `sha224_digest` (`sha224Digest`) calls `Sha224::digest`. On a call satisfying
`OneShot.ValidCall`, it returns and the 28 bytes at RDX are `SHA224 (bytesToBits data)`, the
FIPS 180-4 SHA-224 digest (§6.3) of the message's bits.
-/
theorem sha224_digest_writes_sha224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha224Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha224Digest initial,
          Stack.region initial sha224Digest.minStackBytes] ∧
      OneShot.readOutput sha224Digest initial final = .ok (SHA224 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha224` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha224_digest_slices` (`sha224DigestSlices`) calls `Sha224::new`, then `update` once
per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 28 bytes at RCX are
`SHA224 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-224 digest (§6.3) of the slices' bytes,
concatenated in order.
-/
theorem sha224_digest_slices_writes_sha224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha224DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha224DigestSlices initial,
          Stack.region initial sha224DigestSlices.minStackBytes] ∧
      readOutput sha224DigestSlices initial final =
        .ok (SHA224 (bytesToBits (message inputs))).bytes := by
  sorry

/--
`Digest::digest` for `Sha256` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message in
one call.

The wrapper `sha256_digest` (`sha256Digest`) calls `Sha256::digest`. On a call satisfying
`OneShot.ValidCall`, it returns and the 32 bytes at RDX are `SHA256 (bytesToBits data)`, the
FIPS 180-4 SHA-256 digest (§6.2) of the message's bits.
-/
theorem sha256_digest_writes_sha256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha256Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha256Digest initial,
          Stack.region initial sha256Digest.minStackBytes] ∧
      OneShot.readOutput sha256Digest initial final = .ok (SHA256 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha256` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha256_digest_slices` (`sha256DigestSlices`) calls `Sha256::new`, then `update` once
per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 32 bytes at RCX are
`SHA256 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-256 digest (§6.2) of the slices' bytes,
concatenated in order.
-/
theorem sha256_digest_slices_writes_sha256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha256DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha256DigestSlices initial,
          Stack.region initial sha256DigestSlices.minStackBytes] ∧
      readOutput sha256DigestSlices initial final =
        .ok (SHA256 (bytesToBits (message inputs))).bytes := by
  sorry

/--
`Digest::digest` for `Sha384` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message in
one call.

The wrapper `sha384_digest` (`sha384Digest`) calls `Sha384::digest`. On a call satisfying
`OneShot.ValidCall`, it returns and the 48 bytes at RDX are `SHA384 (bytesToBits data)`, the
FIPS 180-4 SHA-384 digest (§6.5) of the message's bits.
-/
theorem sha384_digest_writes_sha384_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha384Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha384Digest initial,
          Stack.region initial sha384Digest.minStackBytes] ∧
      OneShot.readOutput sha384Digest initial final = .ok (SHA384 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha384` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha384_digest_slices` (`sha384DigestSlices`) calls `Sha384::new`, then `update` once
per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 48 bytes at RCX are
`SHA384 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-384 digest (§6.5) of the slices' bytes,
concatenated in order.
-/
theorem sha384_digest_slices_writes_sha384_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha384DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha384DigestSlices initial,
          Stack.region initial sha384DigestSlices.minStackBytes] ∧
      readOutput sha384DigestSlices initial final =
        .ok (SHA384 (bytesToBits (message inputs))).bytes := by
  sorry

/--
`Digest::digest` for `Sha512` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message in
one call.

The wrapper `sha512_digest` (`sha512Digest`) calls `Sha512::digest`. On a call satisfying
`OneShot.ValidCall`, it returns and the 64 bytes at RDX are `SHA512 (bytesToBits data)`, the
FIPS 180-4 SHA-512 digest (§6.4) of the message's bits.
-/
theorem sha512_digest_writes_sha512_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512Digest initial,
          Stack.region initial sha512Digest.minStackBytes] ∧
      OneShot.readOutput sha512Digest initial final = .ok (SHA512 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha512` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha512_digest_slices` (`sha512DigestSlices`) calls `Sha512::new`, then `update` once
per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 64 bytes at RCX are
`SHA512 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-512 digest (§6.4) of the slices' bytes,
concatenated in order.
-/
theorem sha512_digest_slices_writes_sha512_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512DigestSlices initial,
          Stack.region initial sha512DigestSlices.minStackBytes] ∧
      readOutput sha512DigestSlices initial final =
        .ok (SHA512 (bytesToBits (message inputs))).bytes := by
  sorry

/--
`Digest::digest` for `Sha512_224` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message
in one call.

The wrapper `sha512_224_digest` (`sha512_224Digest`) calls `Sha512_224::digest`. On a call
satisfying `OneShot.ValidCall`, it returns and the 28 bytes at RDX are
`SHA512_224 (bytesToBits data)`, the FIPS 180-4 SHA-512/224 digest (§6.6) of the message's bits.
-/
theorem sha512_224_digest_writes_sha512_224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512_224Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512_224Digest initial,
          Stack.region initial sha512_224Digest.minStackBytes] ∧
      OneShot.readOutput sha512_224Digest initial final =
        .ok (SHA512_224 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha512_224` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha512_224_digest_slices` (`sha512_224DigestSlices`) calls `Sha512_224::new`, then
`update` once per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 28
bytes at RCX are `SHA512_224 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-512/224 digest
(§6.6) of the slices' bytes, concatenated in order.
-/
theorem sha512_224_digest_slices_writes_sha512_224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512_224DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512_224DigestSlices initial,
          Stack.region initial sha512_224DigestSlices.minStackBytes] ∧
      readOutput sha512_224DigestSlices initial final =
        .ok (SHA512_224 (bytesToBits (message inputs))).bytes := by
  sorry

/--
`Digest::digest` for `Sha512_256` (digest 0.11.3, `src/digest.rs:126-130`): hashes a whole message
in one call.

The wrapper `sha512_256_digest` (`sha512_256Digest`) calls `Sha512_256::digest`. On a call
satisfying `OneShot.ValidCall`, it returns and the 32 bytes at RDX are
`SHA512_256 (bytesToBits data)`, the FIPS 180-4 SHA-512/256 digest (§6.7) of the message's bits.
-/
theorem sha512_256_digest_writes_sha512_256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512_256Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512_256Digest initial,
          Stack.region initial sha512_256Digest.minStackBytes] ∧
      OneShot.readOutput sha512_256Digest initial final =
        .ok (SHA512_256 (bytesToBits data)).bytes := by
  sorry

/--
`Digest::new`, `Digest::update` and `Digest::finalize` for `Sha512_256` (digest 0.11.3,
`src/digest.rs:61-63`, `76-78`, `87-89`): hash a message given in parts, feeding a new hasher each
part in order, then taking the digest.

The wrapper `sha512_256_digest_slices` (`sha512_256DigestSlices`) calls `Sha512_256::new`, then
`update` once per slice, then `finalize`. On a call satisfying `ValidCall`, it returns and the 32
bytes at RCX are `SHA512_256 (bytesToBits (message inputs))`, the FIPS 180-4 SHA-512/256 digest
(§6.7) of the slices' bytes, concatenated in order.
-/
theorem sha512_256_digest_slices_writes_sha512_256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512_256DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512_256DigestSlices initial,
          Stack.region initial sha512_256DigestSlices.minStackBytes] ∧
      readOutput sha512_256DigestSlices initial final =
        .ok (SHA512_256 (bytesToBits (message inputs))).bytes := by
  sorry

end Sha2.Statements
