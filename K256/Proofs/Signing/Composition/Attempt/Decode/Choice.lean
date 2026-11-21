import K256.Proofs.Signing.Composition.Attempt.Decode.CallFrame
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Verify.Transfer.Compare

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Sample (blackBox_call)

set_option maxRecDepth 4096 in
theorem choice {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State}
    {a b : Registers} {m n : Ram} {site after : LIR.Label} {ret bx bp p13 p15 : BitVec 64}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (mem : LoopMemory s d msg st n) (regs : RegistersAt s a bx bp p13 p15)
    (path : LIR.program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
      .call ⟨.l127d50,b,n⟩ (resume after ret))
    (keep : ∀ i : Fin Reg.count, i.val ∈ preservedRegisters → b[i] = a[i])
    (rsp : b[4] = ⟨64,sp s-8⟩) (di : b[7] = ⟨64,1⟩) (width14 : b[14].width = 64)
    (widths : ParseSignature.ArgumentWidths b)
    (slot : memLoad n (sp s-8) 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out : Output Value Ram Reg.count,
      Reach (core site a m) (core after out.values out.store) ∧
      LoopMemory s d msg st out.store ∧ RegistersAt s out.values bx bp p13 p15 ∧
      out.values[0] = ⟨64,1⟩ ∧ out.values[14] = b[14] ∧
      RamWriteFrame n out.store [(activation s n b 1 ret).region] := by
  let child := activation s n b 1 ret
  obtain ⟨df,gp,fp⟩ := fixedRegisters regs keep
  have widthsGp (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : b[i].width = 64 := by
    by_cases h : i.val = 14
    · obtain ⟨j,hj⟩ := i
      change j = 14 at h
      subst j
      exact width14
    · exact gp i hi h
  have entry := childAtoms call mem.toMemory Generate.LIR.Fn127d50.frameInfo rfl (by decide) (by decide)
    rsp df widthsGp fp widths slot small
  obtain ⟨out,run,tag,done_,writes,outWidths,flag⟩ :=
    blackBox_call Common.fnCode_subset_programImage child b entry
  have exec : LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,b,n⟩,[]⟩ out :=
    Transfer.verifyExecAt rfl (Verify.Transfer.compareExec rfl run)
  have afterPath := callReaches path exec tag
  have within := childWithin (a:=b) (m:=n) (ret:=ret) (depth:=1) (regions:=[]) call (by decide)
    (by simp only [List.not_mem_nil,false_implies,implies_true])
  have stable := mem.preserve_work call ((RamWriteFrame.refl n _).trans writes within)
  rw [← Generate.LIR.Fn127d50.doneAt_canonical] at done_
  have post := afterCall regs keep done_ outWidths
  simp only [Generate.LIR.Fn127d50.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨_,_,_,_,_,_,r14,_,_,_,_,_⟩ := done_
  refine ⟨out,afterPath,stable,post,?_,r14.trans (value_eq width14).symm,writes⟩
  change out.values[0] = ⟨64,((b[7].get 64).setWidth 8).zeroExtend 64⟩ at flag
  rw [di] at flag
  exact flag

end K256.Proofs.Signing.Composition.Attempt.Decode
