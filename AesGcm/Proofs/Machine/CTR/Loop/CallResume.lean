import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem call_contract_resume {code : CodeMap} {caller callee : LIR.lifted.Location}
    {target label : LIR.Label} {ret : BitVec 64} {output : Output Value Ram Reg.count}
    (hcall : LIR.program.runBlock (dialect code) caller = .call callee
      {target := target, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩})
    (hlabel : callee.label = label)
    (hexec : LIR.program.Exec (dialect code) ⟨⟨label, callee.arguments, callee.store⟩, []⟩ output)
    (htag : output.tag = some ⟨64, ret⟩) :
    (LIR.program.sem (dialect code)).Reaches ⟨caller, []⟩ ⟨⟨target, output.values, output.store⟩, []⟩ := by
  let frame : StackFrame Value LIR.Label signature Reg.count :=
    {target := target, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩}
  have hstep : LIR.program.step (dialect code) ⟨caller, []⟩ = .next ⟨callee, [frame]⟩ := by
    rw [Program.step, hcall]; rfl
  have he : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    cases callee
    subst label
    exact hexec
  have ha : frame.Accepts (dialect code) output.tag = true := by
    rw [htag]; simp [frame, StackFrame.Accepts, dialect]
  have hr := CFGCall.exec_reaches_resume he frame [] ha
  have hn : frame.resume output = ⟨target, output.values, output.store⟩ := by
    have eq := CFGCall.resume_arguments frame output
    cases h : frame.resume output with
    | mk lab vals mem =>
      have hl := congrArg (·.label) h
      have hm := congrArg (·.store) h
      change target = lab at hl
      change output.store = mem at hm
      subst lab mem
      rw [h] at eq
      congr
  rw [hn] at hr
  exact (Semantics.Reaches.single hstep).trans hr

end AesGcm.Proofs.Machine.CTR.Loop
