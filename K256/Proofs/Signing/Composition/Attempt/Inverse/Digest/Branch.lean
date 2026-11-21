import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Branch

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR

theorem digestFillBranch {m : Ram} {a : Verify.Core.Registers} {p : BitVec 64}
    (status : a[0].get 8 = 255) (sp : a[4].get 64 = p) (widths : ParseSignature.ArgumentWidths a) :
    ∃ b : Verify.Core.Registers, Verify.Core.Reaches .l105aaa a m .l105aba b m ∧
      b[13] = ⟨64,p+656⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,14,15,22,39,50,51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?b, .single ?step, ?ptr, ?kept, ?widths⟩
  case step =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [sp, low, cmpSpec_ZF]
    rfl
  case ptr => rfl
  case kept =>
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case widths =>
    intro ⟨i,h⟩ hi
    have wi := widths ⟨i,h⟩ hi
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact wi

end K256.Proofs.Signing.Composition.Attempt.Inverse
