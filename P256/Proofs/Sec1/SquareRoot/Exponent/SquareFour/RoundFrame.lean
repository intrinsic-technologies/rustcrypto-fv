import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Representation
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundCompose

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def roundComponents (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (base + 0x2f0) 8, .mem (base + 0x2e8) 8, .mem (base + 0x70) 8]

theorem round_agrees_broad {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (roundComponents base) s t) : AgreesExcept (components base) s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hn hm
    apply h.agree c _ hm
    intro hc
    apply hn
    simp only [roundComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try contradiction
    all_goals simp [components]
  · intro a hn
    apply h.memory a
    intro c hc hcov
    simp only [roundComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim hcov
    all_goals obtain ⟨i, hi, rfl⟩ := hcov
    all_goals rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add] at hn
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x2f0+i) (by unfold scratchOffset; omega)
      exact hn d hd hv
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x2e8+i) (by unfold scratchOffset; omega)
      exact hn d hd hv
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x70+i) (by unfold scratchOffset; omega)
      exact hn d hd hv

theorem round_read {s t : RamState} {base offset : BitVec 64} {n : Nat}
    (h : AgreesExcept (roundComponents base) s t) (hn : n ≤ 128)
    (h60 : OffsetsApart 0x2f0 8 offset (n/8))
    (hd8 : OffsetsApart 0x2e8 8 offset (n/8))
    (he0 : OffsetsApart 0x70 8 offset (n/8)) :
    (Operand.mem (base + offset) : Operand n).read t =
      (Operand.mem (base + offset) : Operand n).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcov
  simp only [roundComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim hcov
  all_goals obtain ⟨j, hj, he⟩ := hcov
  · exact h60.ne base hj hi (by omega) he.symm
  · exact hd8.ne base hj hi (by omega) he.symm
  · exact he0.ne base hj hi (by omega) he.symm

theorem round_reverse {s t : RamState} {base : BitVec 64} {a : Vector (BitVec 64) 4}
    (h : AgreesExcept (roundComponents base) s t) (hw : ReverseWordsAt s base a) :
    ReverseWordsAt t base a := by
  rcases hw with ⟨h0,h1,h2,h3⟩
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [round_read h (by decide) (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)]
  all_goals assumption

theorem arithmetic_agrees {s t : RamState} {base : BitVec 64}
    (hsp : (Operand.reg 4#5 : Operand 64).read s = base)
    (h : (arithmeticEffect s).Holds s t) :
    AgreesExcept (roundComponents base) s t := by
  apply h.agrees.mono
  intro c hc
  x86_norm [arithmeticEffect, firstProductsEffect, firstCarryEffect, middleFirstEffect,
    middleSecondEffect, topCarryEffect, roundComponents, Bool.or_eq_false_iff, hsp] at hc ⊢
  grind only

theorem arithmetic_index {s t : RamState} (h : (arithmeticEffect s).Holds s t) :
    (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s := by
  apply h.agrees.read
  x86_norm [arithmeticEffect, firstProductsEffect, firstCarryEffect, middleFirstEffect,
    middleSecondEffect, topCarryEffect, Bool.or_eq_false_iff]

end P256.Proofs.Sec1.SquareRoot.SquareFour
