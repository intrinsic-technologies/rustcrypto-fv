import K256.Proofs.Verify.Core.Scalars.State
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Verify.Core.DigestFill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR ParseSignature

theorem branch {mem : Ram} {a : Registers} (status : a[0].get 8 = 255) (widths : ArgumentWidths a) :
    ∃ b : Registers, Reaches .l10513d a mem .l105145 b mem ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      ArgumentWidths b := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?next, .single ?step, ?regs, ?w⟩
  case step =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [low]
    rfl
  case regs =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case w =>
    intro ⟨i, hi⟩ h
    have hw := widths ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

end K256.Proofs.Verify.Core.DigestFill
