import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Coefficient

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

theorem terminalWords {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus}
    {w : Vector Word 4} {d e : Int} (h : Entry a m sp z w)
    (s : LoopState a m sp z 591 b p d e) :
    ∃ neg : Bool, WordsAt p (base sp + 120) 64 (#v[1,0,0,0] : Vector Word 4) ∧
      memLoad p (base sp + 152) 8 = (if neg then 1 else 0) ∧
      ((if neg then -d else d) % (modulus : Int)).toNat = (inverse z).val := by
  have unit : (Core.model z 591).f.natAbs = 1 := SafeGcd.divsteps_591_unit
    (Nat.pos_of_ne_zero h.nonzero) z.isLt
  have inv := SafeGcd.coefficient_inverse h.nonzero unit s.dInvariant
  obtain ⟨v, neg, hv, hs, he⟩ := s.fValue
  have mag : value v = 1 := by cases neg <;> simpa [he] using unit
  have low : v[0] = 1 ∧ v[1] = 0 ∧ v[2] = 0 ∧ v[3] = 0 := by
    unfold value at mag
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> first | (change _ = 1; omega) | (change _ = 0; omega)
  refine ⟨neg, ?_, ?_, ?_⟩
  · have veq : v = #v[1,0,0,0] := by
      apply Vector.ext
      intro i hi
      have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases c with rfl|rfl|rfl|rfl
      all_goals first | exact low.1 | exact low.2.1 | exact low.2.2.1 | exact low.2.2.2
    exact veq ▸ hv
  · rw [show base sp + 152 = base sp + 120 + 32 by bv_omega]; exact hs
  · cases neg <;> simpa [he, mag] using inv

set_option maxRecDepth 4096 in
theorem correctionCallBlock {b : Registers} {p : Ram} {q dst : Word} (neg : Bool)
    (rsp : b[4].get 64 = q)
    (win : Writable Extracted.programImage p (q - 8) 344)
    (ptr : memLoad p (q + 320) 64 = dst)
    (modPtr : memLoad p (q + 160) 64 = 0x2021e0)
    (sign : memLoad p (q + 152) 8 = (if neg then 1 else 0))
    (nonzero : (((memLoad p (q + 312) 64 ||| memLoad p (q + 296) 64) |||
      memLoad p (q + 288) 64) ||| memLoad p (q + 304) 64) ≠ 0) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1093fe, b, p⟩ =
      .call ⟨.l109c00, c, memStore p (q - 8) (0x109448 : Word)⟩ (callFrame .l109448 0x109448) ∧
      c[4] = ⟨64, q - 8⟩ ∧ c[7] = ⟨64, dst⟩ ∧ c[14] = ⟨64, dst⟩ ∧
      c[3].width = 64 ∧ c[3].get 8 = 1 ∧ c[6].get 64 = q + 208 ∧
      c[1].get 64 = 0x2021e0 ∧ (c[2].get 8 &&& 1) = (if neg then 1 else 0) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l1093fe [rsp, ptr, modPtr]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · change (mergeGPR 8 _ _).setWidth 8 = _
      simp [setWidth_mergeGPR8, orFlags]
      intro h₁ h₂ h₃ h₄
      exact nonzero (by simp [h₁, h₂, h₃, h₄])
    · have byte := extractLsb'_memLoad p (q + 152) (n := 32) 0 8 (by decide) (by decide) (by decide)
      change (memLoad p (q + 152) 32).setWidth 8 = memLoad p ((q + 152) + 0) 8 at byte
      rw [show q + 152 + 0 = q + 152 by bv_omega, sign] at byte
      change (((memLoad p (q + 152) 32).setWidth 64).setWidth 8 &&& 1) = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), byte]
      cases neg <;> decide
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Affine.Invert.Core
