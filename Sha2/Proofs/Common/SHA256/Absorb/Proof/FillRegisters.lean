import Sha2.Proofs.Common.SHA256.Absorb.Proof.Registers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem fillSetup_register {l : Layout} {sp : BitVec 64} {s t : RamState} {r : BitVec 4}
    (effect : (Stage.fillSetup.effect l sp s).Holds s t)
    (member : r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4))) (different : r ≠ l.savedSource) :
    Blocks.readReg t r = Blocks.readReg s r := by
  have h := nonvolatile_extended member
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  have different5 : r.setWidth 5 ≠ l.savedSource.setWidth 5 := by
    intro eq
    apply different
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using congrArg BitVec.toNat eq
  apply effect.agrees.read
  simpa [Stage.effect, Effect.components, Write.component, Operand.component] using
    (show r.setWidth 5 ≠ l.savedSource.setWidth 5 ∧ r.setWidth 5 ≠ 7 ∧ r.setWidth 5 ≠ 6 from
      ⟨different5, h.2.2.2.2.1, h.2.2.2.1⟩)

theorem fillCompressSetup_register {l : Layout} {sp : BitVec 64} {s t : RamState} {r : BitVec 4}
    (effect : (Stage.fillCompressSetup.effect l sp s).Holds s t)
    (member : r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4)))
    (different : ∀ q ∈ l.bufferRestore, r ≠ q) : Blocks.readReg t r = Blocks.readReg s r := by
  have h := nonvolatile_extended member
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  apply effect.agrees.read
  cases hr : l.bufferRestore with
  | none =>
    simpa [Stage.effect, hr, Effect.components, Write.component, Operand.component] using
      (show r.setWidth 5 ≠ 2 ∧ r.setWidth 5 ≠ 7 ∧ r.setWidth 5 ≠ 6 from
        ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.1⟩)
  | some q =>
    have ne : r.setWidth 5 ≠ q.setWidth 5 := by
      intro eq
      apply different q (by simp [hr])
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using congrArg BitVec.toNat eq
    simpa [Stage.effect, hr, Effect.components, Write.component, Operand.component] using
      (show r.setWidth 5 ≠ 2 ∧ r.setWidth 5 ≠ 7 ∧ r.setWidth 5 ≠ 6 ∧ r.setWidth 5 ≠ q.setWidth 5 from
        ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.1, ne⟩)

theorem Flow.restored_ne_remaining {l : Layout} (flow : Flow l) {r : BitVec 4}
    (member : r ∈ l.bufferRestore) : r ≠ l.registers.remaining := by
  intro same
  have h := (flow.restoredSaved r member).2 .splitTail (by simp) 0 default
  apply h
  simp [Stage.effect, Blocks.effect, Effect.components, Write.component, Operand.component, same]

end Sha2.Proofs.Common.SHA256.Absorb
