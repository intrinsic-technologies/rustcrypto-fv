import Md5.Spec

set_option warn.sorry false

/-!
# md-5 0.11.0

Theorems about the compiled machine code of md-5 0.11.0, one per wrapper in
`Md5/program/src/lib.rs`, which calls the crate's public methods in a fixed order. Each says that
a well-formed call returns and writes what RFC 1321's MD5 in `Standards/RFC/MD5/` computes.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Md5::digest` | `md5_digest_writes_message_digest` | `MD5.messageDigest` | RFC 1321 §3 |
| `Md5::new`, `Digest::update`, `Digest::finalize` | `md5_digest_slices_writes_message_digest` | `MD5.messageDigest` | RFC 1321 §3 |
| `Md5::new`, `Update::update`, `FixedOutput::finalize_into` | `md5_update_finalize_into_writes_message_digest` | `MD5.messageDigest` | RFC 1321 §3 |
| `Digest::finalize_reset` between two messages | `md5_digest_slices_reset_writes_both_message_digests` | `MD5.messageDigest` of each | RFC 1321 §3 |
| `Digest::finalize_into_reset` between two messages | `md5_finalize_into_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | RFC 1321 §3 |
| `FixedOutputReset::finalize_into_reset` between two messages | `md5_fixed_finalize_into_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | RFC 1321 §3 |
| `FixedOutputReset::finalize_fixed_reset` between two messages | `md5_finalize_fixed_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | RFC 1321 §3 |
| `Digest::reset` between two messages | `md5_reset_slices_writes_second_message_digest` | `MD5.messageDigest` of the second | RFC 1321 §3 |
| `Reset::reset` between two messages | `md5_update_reset_slices_writes_second_message_digest` | `MD5.messageDigest` of the second | RFC 1321 §3 |
| `md5::block_api::compress` | `md5_compress_writes_buffer_after_blocks` | `MD5.processBlocks` | RFC 1321 §3.4 |

Each theorem docstring below names the theorem's call predicate; every theorem also assumes the
machine conditions `hMachine` and `hBindings`, which the README describes.

How to read the theorem statements and how to build the verified binary are in `Md5/README.md`.
-/

namespace Md5.Statements

open Md5.Spec Md5.Spec.Program Prelude X86 Standards.RFC

/--
`Md5::digest` (digest 0.11.3, `src/digest.rs:126-130`): hashes a message in one call.

On a call satisfying `Digest.ValidCall`, it returns and `Digest.readOutput` gives
`MD5.messageDigest (MD5.bitsOfBytes input)`, the 16-byte RFC 1321 digest (§3) of `input`.
-/
theorem md5_digest_writes_message_digest
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
      Digest.readOutput initial final = .ok (MD5.messageDigest (MD5.bitsOfBytes input)) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` per slice
(`src/digest.rs:76-78`), then `Digest::finalize` (`src/digest.rs:87-89`): hashes a message given
in parts.

On a call satisfying `OneMessage.ValidCall`, it returns and `OneMessage.readOutput` gives the
16-byte RFC 1321 digest (§3) of `Slices.message inputs`, the slices joined in order.
-/
theorem md5_digest_slices_writes_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneMessage.ValidCall OneMessage.digestSlices bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneMessage.outputRegion OneMessage.digestSlices initial,
          Stack.region initial OneMessage.digestSlices.minStackBytes] ∧
      OneMessage.readOutput OneMessage.digestSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.message inputs))) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Update::update` per slice
(`src/buffer_macros/fixed.rs:202-207`), then `FixedOutput::finalize_into`
(`src/buffer_macros/fixed.rs:222-225`): hashes a message given in parts through the `Update` and
`FixedOutput` traits, writing the digest into the caller's array.

On a call satisfying `OneMessage.ValidCall`, it returns and `OneMessage.readOutput` gives the
16-byte RFC 1321 digest (§3) of `Slices.message inputs`, the slices joined in order.
-/
theorem md5_update_finalize_into_writes_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneMessage.ValidCall OneMessage.updateFinalizeInto bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneMessage.outputRegion OneMessage.updateFinalizeInto initial,
          Stack.region initial OneMessage.updateFinalizeInto.minStackBytes] ∧
      OneMessage.readOutput OneMessage.updateFinalizeInto initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.message inputs))) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` per slice
(`src/digest.rs:76-78`), `Digest::finalize_reset` (`src/digest.rs:97-102`) after the first
message, then `Digest::finalize` (`src/digest.rs:87-89`): hashes two messages with one hasher,
which `finalize_reset` starts afresh.

On a call satisfying `TwoMessages.ValidCall`, it returns and `TwoMessages.readOutput` gives 32
bytes: the RFC 1321 digest (§3) of `Slices.firstMessage inputs first`, then that of
`Slices.secondMessage inputs first`.
-/
theorem md5_digest_slices_reset_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : TwoMessages.ValidCall TwoMessages.digestSlicesReset bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.digestSlicesReset initial,
          Stack.region initial TwoMessages.digestSlicesReset.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.digestSlicesReset initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Digest::update` per slice
(`src/digest.rs:76-78`), `Digest::finalize_into_reset` (`src/digest.rs:105-110`) after the first
message, then `Digest::finalize` (`src/digest.rs:87-89`): hashes two messages with one hasher,
writing the first digest into the caller's array and starting the hasher afresh.

On a call satisfying `TwoMessages.ValidCall`, it returns and `TwoMessages.readOutput` gives 32
bytes: the RFC 1321 digest (§3) of `Slices.firstMessage inputs first`, then that of
`Slices.secondMessage inputs first`.
-/
theorem md5_finalize_into_reset_slices_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.finalizeIntoResetSlices initial,
          Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.finalizeIntoResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Update::update` per slice
(`src/buffer_macros/fixed.rs:202-207`), `FixedOutputReset::finalize_into_reset`
(`src/buffer_macros/fixed.rs:411-415`) after the first message, then `Digest::finalize`
(`src/digest.rs:87-89`): hashes two messages with one hasher through the `Update` and
`FixedOutputReset` traits, writing the first digest into the caller's array and starting the
hasher afresh.

On a call satisfying `TwoMessages.ValidCall`, it returns and `TwoMessages.readOutput` gives 32
bytes: the RFC 1321 digest (§3) of `Slices.firstMessage inputs first`, then that of
`Slices.secondMessage inputs first`.
-/
theorem md5_fixed_finalize_into_reset_slices_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      TwoMessages.ValidCall TwoMessages.fixedFinalizeIntoResetSlices bindings initial inputs
        first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.fixedFinalizeIntoResetSlices initial,
          Stack.region initial TwoMessages.fixedFinalizeIntoResetSlices.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.fixedFinalizeIntoResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`Md5::new` (digest 0.11.3, `src/digest.rs:61-63`), `Update::update` per slice
(`src/buffer_macros/fixed.rs:202-207`), `FixedOutputReset::finalize_fixed_reset` (digest 0.11.3,
`src/lib.rs:116-120`) after the first message, then `Digest::finalize` (`src/digest.rs:87-89`):
hashes two messages with one hasher through the `Update` and `FixedOutputReset` traits, starting
the hasher afresh after the first.

On a call satisfying `TwoMessages.ValidCall`, it returns and `TwoMessages.readOutput` gives 32
bytes: the RFC 1321 digest (§3) of `Slices.firstMessage inputs first`, then that of
`Slices.secondMessage inputs first`.
-/
theorem md5_finalize_fixed_reset_slices_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      TwoMessages.ValidCall TwoMessages.finalizeFixedResetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.finalizeFixedResetSlices initial,
          Stack.region initial TwoMessages.finalizeFixedResetSlices.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.finalizeFixedResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`Digest::update` per slice (digest 0.11.3, `src/digest.rs:76-78`), `Digest::reset`
(`src/digest.rs:113-118`) after the first message, then `Digest::finalize`
(`src/digest.rs:87-89`): discards what the hasher has taken in, then hashes the second message.

On a call satisfying `ResetThenDigest.ValidCall`, it returns and `ResetThenDigest.readOutput` gives
the 16-byte RFC 1321 digest (§3) of `Slices.secondMessage inputs first` alone, so the reset is
observed. The wrapper also calls `Md5::new`, but the reset discards what it made; the theorems
without a reset cover it.
-/
theorem md5_reset_slices_writes_second_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ResetThenDigest.ValidCall ResetThenDigest.resetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[ResetThenDigest.outputRegion ResetThenDigest.resetSlices initial,
          Stack.region initial ResetThenDigest.resetSlices.minStackBytes] ∧
      ResetThenDigest.readOutput ResetThenDigest.resetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`Update::update` per slice (digest 0.11.3, `src/buffer_macros/fixed.rs:202-207`), `Reset::reset`
(`src/buffer_macros/fixed.rs:391-397`) after the first message, then `Digest::finalize`
(`src/digest.rs:87-89`): discards what the hasher has taken in, then hashes the second message.

On a call satisfying `ResetThenDigest.ValidCall`, it returns and `ResetThenDigest.readOutput` gives
the 16-byte RFC 1321 digest (§3) of `Slices.secondMessage inputs first` alone, so the reset is
observed. The wrapper also calls `Md5::new`, but the reset discards what it made; the theorems
without a reset cover it.
-/
theorem md5_update_reset_slices_writes_second_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[ResetThenDigest.outputRegion ResetThenDigest.updateResetSlices initial,
          Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes] ∧
      ResetThenDigest.readOutput ResetThenDigest.updateResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  sorry

/--
`md5::block_api::compress` (md-5 0.11.0, `src/compress.rs:15-17`): updates the four state words
with each 64-byte block in turn.

On a call satisfying `Compress.ValidCall`, it returns and `Compress.readOutput` gives
`MD5.processBlocks buffer (MD5.wordsOfBytes blocks)`, the MD buffer after RFC 1321's loop over every
block (§3.4), as 16 bytes, each word low-order byte first (`MD5.Buffer.toBytes`). The MD buffer at
RDI is read and overwritten.
-/
theorem md5_compress_writes_buffer_after_blocks
    {initial : Machine.RamState} {buffer : MD5.Buffer} {blocks : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial buffer blocks) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (MD5.processBlocks buffer (MD5.wordsOfBytes blocks)).toBytes := by
  sorry

end Md5.Statements
