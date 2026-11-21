import Sha3.Spec

set_option warn.sorry false

/-!
# sha3 0.12.0

Theorems about the compiled machine code of sha3 0.12.0, two per hasher: `Digest::digest` of the
data, and `Digest::new`, `Digest::update` per slice and `Digest::finalize` over a message given in
slices. Each says that a well-formed call returns and writes the digest the specification computes:
the FIPS 202 functions in `Standards/NIST/SHA3/` for SHA-3, and for Keccak the specifications in
`Sha3/Spec/Keccak.lean`, built on the same FIPS 202 functions.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Sha3_224::digest`; `Sha3_224::new`, `update`, `finalize` | `sha3_224_digest_writes_sha3_224_of_data`; `sha3_224_digest_slices_writes_sha3_224_of_message` | `SHA3.SHA3_224` | FIPS 202 §6.1 |
| `Sha3_256::digest`; `Sha3_256::new`, `update`, `finalize` | `sha3_256_digest_writes_sha3_256_of_data`; `sha3_256_digest_slices_writes_sha3_256_of_message` | `SHA3.SHA3_256` | FIPS 202 §6.1 |
| `Sha3_384::digest`; `Sha3_384::new`, `update`, `finalize` | `sha3_384_digest_writes_sha3_384_of_data`; `sha3_384_digest_slices_writes_sha3_384_of_message` | `SHA3.SHA3_384` | FIPS 202 §6.1 |
| `Sha3_512::digest`; `Sha3_512::new`, `update`, `finalize` | `sha3_512_digest_writes_sha3_512_of_data`; `sha3_512_digest_slices_writes_sha3_512_of_message` | `SHA3.SHA3_512` | FIPS 202 §6.1 |
| `Keccak224::digest`; `Keccak224::new`, `update`, `finalize` | `keccak224_digest_writes_keccak224_of_data`; `keccak224_digest_slices_writes_keccak224_of_message` | `Keccak.keccak224` | Keccak submission v3 §2 |
| `Keccak256::digest`; `Keccak256::new`, `update`, `finalize` | `keccak256_digest_writes_keccak256_of_data`; `keccak256_digest_slices_writes_keccak256_of_message` | `Keccak.keccak256` | Keccak submission v3 §2 |
| `Keccak384::digest`; `Keccak384::new`, `update`, `finalize` | `keccak384_digest_writes_keccak384_of_data`; `keccak384_digest_slices_writes_keccak384_of_message` | `Keccak.keccak384` | Keccak submission v3 §2 |
| `Keccak512::digest`; `Keccak512::new`, `update`, `finalize` | `keccak512_digest_writes_keccak512_of_data`; `keccak512_digest_slices_writes_keccak512_of_message` | `Keccak.keccak512` | Keccak submission v3 §2 |

Each theorem docstring below names the theorem's call predicate; every theorem also assumes the
machine conditions `hMachine` and `hBindings`, which the README describes.

How to read the theorem statements and how to build the verified binary are in `Sha3/README.md`.
-/

namespace Sha3.Statements

open Sha3.Spec Sha3.Spec.Program Standards.NIST Prelude X86

/--
`Digest::digest` for `Sha3_224` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `sha3_224_digest` calls `Sha3_224::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 28 bytes at RDX hold `SHA3.SHA3_224` (FIPS 202, §6.1) of `SHA3.bytesToBits data`,
packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_224_digest_writes_sha3_224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_224_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_224_digest initial,
          Stack.region initial sha3_224_digest.minStackBytes] ∧
      readDigestOutput sha3_224_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_224 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Sha3_224`: hashes a
message given in slices.

The wrapper `sha3_224_digest_slices` calls `Sha3_224::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 28 bytes at RCX hold
`SHA3.SHA3_224` (FIPS 202, §6.1) of `SHA3.bytesToBits` of `message inputs`, the slices joined in
order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_224_digest_slices_writes_sha3_224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_224_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_224_digest_slices initial,
          Stack.region initial sha3_224_digest_slices.minStackBytes] ∧
      readOutput sha3_224_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_224 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Sha3_256` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `sha3_256_digest` calls `Sha3_256::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 32 bytes at RDX hold `SHA3.SHA3_256` (FIPS 202, §6.1) of `SHA3.bytesToBits data`,
packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_256_digest_writes_sha3_256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_256_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_256_digest initial,
          Stack.region initial sha3_256_digest.minStackBytes] ∧
      readDigestOutput sha3_256_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_256 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Sha3_256`: hashes a
message given in slices.

The wrapper `sha3_256_digest_slices` calls `Sha3_256::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 32 bytes at RCX hold
`SHA3.SHA3_256` (FIPS 202, §6.1) of `SHA3.bytesToBits` of `message inputs`, the slices joined in
order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_256_digest_slices_writes_sha3_256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_256_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_256_digest_slices initial,
          Stack.region initial sha3_256_digest_slices.minStackBytes] ∧
      readOutput sha3_256_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_256 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Sha3_384` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `sha3_384_digest` calls `Sha3_384::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 48 bytes at RDX hold `SHA3.SHA3_384` (FIPS 202, §6.1) of `SHA3.bytesToBits data`,
packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_384_digest_writes_sha3_384_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_384_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_384_digest initial,
          Stack.region initial sha3_384_digest.minStackBytes] ∧
      readDigestOutput sha3_384_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_384 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Sha3_384`: hashes a
message given in slices.

The wrapper `sha3_384_digest_slices` calls `Sha3_384::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 48 bytes at RCX hold
`SHA3.SHA3_384` (FIPS 202, §6.1) of `SHA3.bytesToBits` of `message inputs`, the slices joined in
order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_384_digest_slices_writes_sha3_384_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_384_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_384_digest_slices initial,
          Stack.region initial sha3_384_digest_slices.minStackBytes] ∧
      readOutput sha3_384_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_384 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Sha3_512` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `sha3_512_digest` calls `Sha3_512::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 64 bytes at RDX hold `SHA3.SHA3_512` (FIPS 202, §6.1) of `SHA3.bytesToBits data`,
packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_512_digest_writes_sha3_512_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_512_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_512_digest initial,
          Stack.region initial sha3_512_digest.minStackBytes] ∧
      readDigestOutput sha3_512_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_512 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Sha3_512`: hashes a
message given in slices.

The wrapper `sha3_512_digest_slices` calls `Sha3_512::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 64 bytes at RCX hold
`SHA3.SHA3_512` (FIPS 202, §6.1) of `SHA3.bytesToBits` of `message inputs`, the slices joined in
order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem sha3_512_digest_slices_writes_sha3_512_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_512_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_512_digest_slices initial,
          Stack.region initial sha3_512_digest_slices.minStackBytes] ∧
      readOutput sha3_512_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_512 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Keccak224` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `keccak224_digest` calls `Keccak224::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 28 bytes at RDX hold `Keccak.keccak224` (Keccak submission, §2) of
`SHA3.bytesToBits data`, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak224_digest_writes_keccak224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak224_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak224_digest initial,
          Stack.region initial keccak224_digest.minStackBytes] ∧
      readDigestOutput keccak224_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak224 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Keccak224`: hashes a
message given in slices.

The wrapper `keccak224_digest_slices` calls `Keccak224::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 28 bytes at RCX hold
`Keccak.keccak224` (Keccak submission, §2) of `SHA3.bytesToBits` of `message inputs`, the slices
joined in order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak224_digest_slices_writes_keccak224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak224_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak224_digest_slices initial,
          Stack.region initial keccak224_digest_slices.minStackBytes] ∧
      readOutput keccak224_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak224 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Keccak256` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `keccak256_digest` calls `Keccak256::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 32 bytes at RDX hold `Keccak.keccak256` (Keccak submission, §2) of
`SHA3.bytesToBits data`, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak256_digest_writes_keccak256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak256_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak256_digest initial,
          Stack.region initial keccak256_digest.minStackBytes] ∧
      readDigestOutput keccak256_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak256 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Keccak256`: hashes a
message given in slices.

The wrapper `keccak256_digest_slices` calls `Keccak256::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 32 bytes at RCX hold
`Keccak.keccak256` (Keccak submission, §2) of `SHA3.bytesToBits` of `message inputs`, the slices
joined in order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak256_digest_slices_writes_keccak256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak256_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak256_digest_slices initial,
          Stack.region initial keccak256_digest_slices.minStackBytes] ∧
      readOutput keccak256_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak256 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Keccak384` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `keccak384_digest` calls `Keccak384::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 48 bytes at RDX hold `Keccak.keccak384` (Keccak submission, §2) of
`SHA3.bytesToBits data`, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak384_digest_writes_keccak384_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak384_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak384_digest initial,
          Stack.region initial keccak384_digest.minStackBytes] ∧
      readDigestOutput keccak384_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak384 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Keccak384`: hashes a
message given in slices.

The wrapper `keccak384_digest_slices` calls `Keccak384::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 48 bytes at RCX hold
`Keccak.keccak384` (Keccak submission, §2) of `SHA3.bytesToBits` of `message inputs`, the slices
joined in order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak384_digest_slices_writes_keccak384_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak384_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak384_digest_slices initial,
          Stack.region initial keccak384_digest_slices.minStackBytes] ∧
      readOutput keccak384_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak384 (SHA3.bytesToBits (message inputs)))) := by
  sorry

/--
`Digest::digest` for `Keccak512` (digest 0.11.3, `src/digest.rs:126-130`): hashes the data in one
call.

The wrapper `keccak512_digest` calls `Keccak512::digest`. On a call satisfying `ValidDigestCall`, it
returns and the 64 bytes at RDX hold `Keccak.keccak512` (Keccak submission, §2) of
`SHA3.bytesToBits data`, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak512_digest_writes_keccak512_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak512_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak512_digest initial,
          Stack.region initial keccak512_digest.minStackBytes] ∧
      readDigestOutput keccak512_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak512 (SHA3.bytesToBits data))) := by
  sorry

/--
`Digest::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` once per slice
(`src/digest.rs:76-78`) and `Digest::finalize` (`src/digest.rs:87-89`) for `Keccak512`: hashes a
message given in slices.

The wrapper `keccak512_digest_slices` calls `Keccak512::new`, then `update` once per slice, then
`finalize`. On a call satisfying `ValidCall`, it returns and the 64 bytes at RCX hold
`Keccak.keccak512` (Keccak submission, §2) of `SHA3.bytesToBits` of `message inputs`, the slices
joined in order, packed into bytes by `SHA3.Digest.ofBits`.
-/
theorem keccak512_digest_slices_writes_keccak512_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak512_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak512_digest_slices initial,
          Stack.region initial keccak512_digest_slices.minStackBytes] ∧
      readOutput keccak512_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak512 (SHA3.bytesToBits (message inputs)))) := by
  sorry

end Sha3.Statements
