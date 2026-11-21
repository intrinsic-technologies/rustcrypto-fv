import Sha1.Spec

set_option warn.sorry false

/-!
# sha1 0.11.0

Theorems about the compiled machine code of sha1 0.11.0: one for the one-shot `Sha1::digest` and
one for the sequence `Sha1::new`, `update`, `finalize`. Each says that a well-formed call returns
and writes the FIPS 180-4 SHA-1 digest that `SHA1.SHA1` in `Standards/NIST/SHA1` computes, with no
crate specification in between.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Sha1::digest` | `sha1_digest_writes_digest_of_input` | `SHA1.SHA1` | FIPS 180-4 §6.1 |
| `Sha1::new`, `update`, `finalize` | `sha1_update_finalize_writes_digest_of_inputs` | `SHA1.SHA1` | FIPS 180-4 §6.1 |

Each theorem docstring below names the theorem's call predicate; every theorem also assumes the
machine conditions `hMachine` and `hBindings`, which the README describes.

How to read the theorem statements and how to build the verified binary are in `Sha1/README.md`.
-/

namespace Sha1.Statements

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86

/--
`Sha1::digest` (digest 0.11.3, `src/digest.rs:126-130`): hashes a message in one call, giving its
20-byte SHA-1 digest.

The wrapper `sha1_digest` calls `Sha1::digest` on the input and copies the digest to the output.
On a call satisfying `Digest.ValidCall`, it returns and the 20 bytes at RDX are `SHA1.SHA1`
(FIPS 180-4 §6.1) of the input's bits, each byte most significant bit first (`SHA2.bytesToBits`).
-/
theorem sha1_digest_writes_digest_of_input
    {initial : Machine.RamState} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final = .ok (SHA1.SHA1 (SHA2.bytesToBits input)).bytes := by
  sorry

/--
`Sha1::new` (digest 0.11.3, `src/digest.rs:61-63`), `Sha1::update` (`src/digest.rs:76-78`) and
`Sha1::finalize` (`src/digest.rs:87-89`): hash a message given in parts, feeding a new `Sha1` each
part in order and finishing with the 20-byte digest.

The wrapper `sha1_update_finalize` (`SliceHash.updateFinalize`) calls `Sha1::new`, `update` once
per slice in order, and `finalize`. On a call satisfying `SliceHash.ValidCall`, it returns and the
20 bytes at RCX are `SHA1.SHA1` (FIPS 180-4 §6.1) of the bits of `Slices.message inputs`, the
slices joined in order.
-/
theorem sha1_update_finalize_writes_digest_of_inputs
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
          Stack.region initial SliceHash.updateFinalize.minStackBytes] ∧
      SliceHash.readOutput SliceHash.updateFinalize initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits (Slices.message inputs))).bytes := by
  sorry

end Sha1.Statements
