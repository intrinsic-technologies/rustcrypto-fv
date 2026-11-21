import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn1034c0.Frame

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem preserved_of_doneAtoms (code : CodeMap) (mem : Ram)
    (args : Values Value Reg.count) (ret low : BitVec 64)
    (output : Output Value Ram Reg.count)
    (hTypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hdf : args[22] = ⟨1, 0⟩)
    (hdone : Atom.All code output.values output.store
      (LIR.Fn1034c0.frameInfo.doneAtoms (activationOfValues mem args ret low))) :
    output.values[4] = ⟨64, args[4].get 64 + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        output.values[r] = args[r]) := by
  change output.values[4] = ⟨64, args[4].get 64 + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
    output.values[3] = ⟨64, args[3].get 64⟩ ∧ output.values[5] = ⟨64, args[5].get 64⟩ ∧
    output.values[12] = ⟨64, args[12].get 64⟩ ∧ output.values[13] = ⟨64, args[13].get 64⟩ ∧
    output.values[14] = ⟨64, args[14].get 64⟩ ∧ output.values[15] = ⟨64, args[15].get 64⟩ ∧
    output.values[39] = ⟨32, args[39].get 32⟩ ∧ output.values[50] = ⟨16, args[50].get 16⟩ ∧
    output.values[51] = ⟨16, args[51].get 16⟩ ∧ True at hdone
  rcases hdone with ⟨h4, h22, h3, h5, h12, h13, h14, h15, hf39, hf50, hf51, -⟩
  refine ⟨h4, ?_⟩
  rintro ⟨r, hr⟩ hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3.trans (hTypes.value ⟨3, by decide⟩).symm
  · exact h5.trans (hTypes.value ⟨5, by decide⟩).symm
  · exact h12.trans (hTypes.value ⟨12, by decide⟩).symm
  · exact h13.trans (hTypes.value ⟨13, by decide⟩).symm
  · exact h14.trans (hTypes.value ⟨14, by decide⟩).symm
  · exact h15.trans (hTypes.value ⟨15, by decide⟩).symm
  · exact h22.trans hdf.symm
  · exact hf39.trans h39.symm
  · exact hf50.trans h50.symm
  · exact hf51.trans h51.symm

theorem call_reaches (code : CodeMap) (caller callee : LIR.lifted.Location)
    (continuation : StackFrame Value LIR.Label (fun _ ↦ Reg.count) Reg.count)
    (output : Output Value Ram Reg.count)
    (hcall : LIR.program.runBlock (dialect code) caller = .call callee continuation)
    (hexec : LIR.program.Exec (dialect code) ⟨callee, []⟩ output)
    (haccept : continuation.Accepts (dialect code) output.tag = true) :
    (LIR.program.sem (dialect code)).Reaches ⟨caller, []⟩
      ⟨⟨continuation.target, output.values, output.store⟩, []⟩ := by
  have hnext : LIR.program.step (dialect code) ⟨caller, []⟩ =
      .next ⟨callee, [continuation]⟩ := by
    rw [Program.step, hcall]
    rfl
  have resume : (LIR.program.sem (dialect code)).Reaches
      ⟨callee, [continuation]⟩ ⟨continuation.resume output, []⟩ :=
    CFGCall.exec_reaches_resume hexec continuation [] haccept
  have he : continuation.resume output =
      (⟨continuation.target, output.values, output.store⟩ : LIR.lifted.Location) := by
    have hargs := CFGCall.resume_arguments continuation output
    exact congrArg (fun values : Values Value Reg.count ↦
      (⟨continuation.target, values, output.store⟩ : LIR.lifted.Location)) hargs
  rw [he] at resume
  exact (Semantics.Reaches.single hnext).trans resume

end AesGcm.Proofs.Machine.Tag.Execution
