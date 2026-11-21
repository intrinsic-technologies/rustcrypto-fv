import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Generate.Generator.Sample.Decode.Scalar
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Compare

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

noncomputable abbrev Reaches (a b : Location Value Ram LIR.Label signature) :=
  (LIR.program.sem (dialect Extracted.programImage)).Reaches ⟨a, []⟩ ⟨b, []⟩

theorem resumeCall {caller callee : Location Value Ram LIR.Label signature}
    {resume : LIR.Label} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (push : LIR.program.runBlock (dialect Extracted.programImage) caller =
      .call callee ⟨resume, #v[], rfl, some ⟨64, ret⟩⟩)
    (run : LIR.program.Exec (dialect Extracted.programImage) ⟨callee, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) : Reaches caller ⟨resume, out.values, out.store⟩ := by
  let frame : StackFrame Value LIR.Label signature Reg.count := ⟨resume, #v[], rfl, some ⟨64, ret⟩⟩
  refine .step (b := ⟨callee, [frame]⟩) ?_ ?_
  · change (LIR.program.runBlock _ _).next _ _ = _
    rw [push]
    rfl
  · exact ParseSignature.exec_reaches_resume run frame [] (by
      rw [tag]
      exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))

end K256.Proofs.Ecdh.Scalar
