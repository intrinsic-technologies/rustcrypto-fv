import Hkdf.Proofs.NewExpand.Expand.Positive.Setup
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem positive [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (state : DispatchState entry s boundary length) (pos : 0 < length) (bound : length ≤ 8160) :
    ∃ t, SavedFrame entry t boundary length ∧ t.RIP = 0x10f290 ∧
      ∃ bytes, RFC5869.expandFromPrk .sha256 key info length = .ok bytes ∧
        (registerRegion entry .rcx length).HasBytes t.external bytes := by
  have rounds (n : Nat) (hn : n ≤ (length + 31) / 32) :
      ∃ t, LoopState entry t boundary key info length n := by
    induction n with
    | zero => exact startLoop pre state pos bound
    | succ n ih =>
      obtain ⟨t, head⟩ := ih (by omega)
      exact iterate pre head (by omega) bound
  let count := (length + 31) / 32
  obtain ⟨t, last⟩ := rounds count (Nat.le_refl _)
  have complete : length ≤ 32 * count := by dsimp only [count]; omega
  refine ⟨t, last.toSavedFrame, ?_, (blocks .sha256 key info count).1.extract 0 length, ?_, ?_⟩
  · simpa only [Nat.not_lt.mpr complete, ↓reduceIte] using last.pc
  · exact expandFromPrk_sha256_blocks (Nat.le_of_eq pre.keySize.symm) bound
  · simpa only [Nat.min_eq_right complete] using last.output

end Hkdf.Proofs.NewExpand.Expand
