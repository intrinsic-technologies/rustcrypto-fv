import Sha2.Proofs.Common.Machine.Epilogue

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine.Epilogue

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem calleeSaved {initial s u t : RamState} {p : BitVec 64} {layout : Layout}
    (restored : (effect p layout s).Holds s u) (returned : (retEffect u).Holds u t)
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (savedRbp : if layout.six then
      memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 40)) 64 =
        (Operand.reg 5 : Operand 64).read initial
      else (Operand.reg 5 : Operand 64).read s = (Operand.reg 5 : Operand 64).read initial) :
    CalleeSavedRegistersUnchanged initial t := by
  have finalFrame : AgreesExcept [.reg 4, .rip] u t := returned.agrees
  have writes := Write.allHold_iff.mp restored.writes
  intro register member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · change (Operand.reg 3 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    exact (writes (⟨(.reg 3 : Operand 64), memLoad s.external
      (rspOf s + BitVec.ofNat 64 (layout.allocation + 0)) 64⟩ : Write)
      (by simp [effect])).trans (saved 3 0 (by simp))
  · change (Operand.reg 5 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    cases layout with
    | five272 =>
      rw [restored.agrees.read (by simp [effect, Layout.six, Effect.components, Write.component, Operand.component])]
      exact savedRbp
    | six200 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six200.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
    | six312 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six312.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
    | six552 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six552.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
    | six376 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six376.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
    | six584 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six584.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
    | six600 =>
      exact (writes (⟨(.reg 5 : Operand 64), memLoad s.external
        (rspOf s + BitVec.ofNat 64 (Layout.six600.allocation + 40)) 64⟩ : Write)
        (by simp [effect, Layout.six])).trans savedRbp
  · change (Operand.reg 12 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    exact (writes (⟨(.reg 12 : Operand 64), memLoad s.external
      (rspOf s + BitVec.ofNat 64 (layout.allocation + 8)) 64⟩ : Write)
      (by simp [effect])).trans (saved 12 8 (by simp))
  · change (Operand.reg 13 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    exact (writes (⟨(.reg 13 : Operand 64), memLoad s.external
      (rspOf s + BitVec.ofNat 64 (layout.allocation + 16)) 64⟩ : Write)
      (by simp [effect])).trans (saved 13 16 (by simp))
  · change (Operand.reg 14 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    exact (writes (⟨(.reg 14 : Operand 64), memLoad s.external
      (rspOf s + BitVec.ofNat 64 (layout.allocation + 24)) 64⟩ : Write)
      (by simp [effect])).trans (saved 14 24 (by simp))
  · change (Operand.reg 15 : Operand 64).read t = _
    rw [finalFrame.read (by simp)]
    exact (writes (⟨(.reg 15 : Operand 64), memLoad s.external
      (rspOf s + BitVec.ofNat 64 (layout.allocation + 32)) 64⟩ : Write)
      (by simp [effect])).trans (saved 15 32 (by simp))

end Sha2.Proofs.Common.Machine.Epilogue
