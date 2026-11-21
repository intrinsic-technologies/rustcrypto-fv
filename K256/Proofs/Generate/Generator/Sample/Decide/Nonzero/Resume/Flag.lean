import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Generator.Sample.State
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev nonzeroPreserved := [3, 5, 12, 13, 14, 15, 22, 39, 50, 51]

theorem complementCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (w : Writable Extracted.programImage m (sp - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105ff5, a, m⟩ =
        .call ⟨.l127d50, b, memStore m (sp - 8) (0x106001 : BitVec 64)⟩
          (callFrame .l106001 0x106001) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[7] = ⟨64, ((~~~(a[0].get 8)) &&& 1).setWidth 64⟩ ∧
      ParseSignature.ArgumentWidths b ∧
      ∀ j : Fin Reg.count, j.val ∈ nonzeroPreserved → b[j] = a[j] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x105ffc 5 := by
    slot_guard using code_l105ff5
  have low : (a[0].get 64).setWidth 8 = a[0].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l105ff5 [rsp, push]
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · change Value.mk 64 ((mergeGPR 8 _ _).setWidth 8 |>.setWidth 64) = _
      simp only [setWidth_mergeGPR8, low]
    · intro ⟨j, hj⟩ h
      have width := widths ⟨j, hj⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact width
    · intro ⟨j, hj⟩ h
      simp only [nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem reachesAfterSampleCall {caller callee : Location Value Ram Label signature}
    {resume : Label} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (push : program.runBlock (dialect Extracted.programImage) caller = .call callee (callFrame resume ret))
    (run : program.Exec (dialect Extracted.programImage) ⟨callee, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) (stack : List (StackFrame Value Label signature Reg.count)) :
    Run.Reaches ⟨caller, stack⟩ ⟨⟨resume, out.values, out.store⟩, stack⟩ := by
  refine .step (b := ⟨callee, callFrame resume ret :: stack⟩) ?_ ?_
  · change (program.runBlock _ _).next _ _ = _
    rw [push]
    rfl
  · have accepts : (callFrame resume ret).Accepts (dialect Extracted.programImage) out.tag = true := by
      rw [tag]
      exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret)
    exact ParseSignature.exec_reaches_resume run _ stack accepts

end K256.Proofs.Generate.Generator.Sample
