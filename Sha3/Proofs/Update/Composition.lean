import Sha3.Proofs.Update.Frame
import Sha3.Proofs.Incremental.Canonical

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem update_split (permute : Keccak.Lanes → Keccak.Lanes) (rate : Nat)
    (state : Incremental.State) (bytes : ByteArray) (offset : Nat) (h : offset ≤ bytes.size) :
    Incremental.update permute rate state bytes =
      Incremental.update permute rate
        (Incremental.update permute rate state (bytes.extract 0 offset))
        (bytes.extract offset bytes.size) := by
  rw [← Incremental.update_append, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right h, ByteArray.extract_zero_size]

theorem state_eq_zero_cursor {state : Incremental.State} (h : state.cursor = 0) :
    state = ⟨state.lanes, 0⟩ := by
  cases state
  cases h
  rfl

theorem CallResult.programLoaded [Bindings] {v : Variant} {initial final : RamState}
    {bytes : ByteArray} {state result : Incremental.State}
    (hc : CallContext v initial bytes state) (hr : CallResult initial final result) :
    ProgramLoaded final := by
  apply programLoaded_of_memoryWriteFrame hr.memory _ hc.loaded
  intro region hregion address ha hprogram
  exact hc.avoids region hregion address ha (.inl hprogram)

end Sha3.Proofs.Update
