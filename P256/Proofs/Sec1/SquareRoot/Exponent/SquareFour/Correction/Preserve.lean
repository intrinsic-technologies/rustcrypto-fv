import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Support

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem saved_window {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) :
    (Operand.mem (base + 0x2d0) : Operand 64).read t =
      (Operand.mem (base + 0x2d0) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcover
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  all_goals obtain ⟨j,hj,he⟩ := hcover
  all_goals exact OffsetsApart.ne (base := base) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he

theorem saved_counter {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) :
    (Operand.mem (base + 0x7c) : Operand 32).read t =
      (Operand.mem (base + 0x7c) : Operand 32).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcover
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  all_goals obtain ⟨j,hj,he⟩ := hcover
  all_goals exact OffsetsApart.ne (base := base) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
