import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.Affine.Uncompressed.Entry

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

theorem resumeChoice {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code)
    {caller : Location Value Ram Label signature} {target : Label} {ret sp : Word}
    {args : Values Value Reg.count} {m : Ram}
    (step : program.runBlock (dialect code) caller =
      .call ⟨.l127d50,args,m⟩ (choiceResume target ret rfl))
    (rsp : args[4].get 64 = sp - 8) (stack : Writable code m (sp - 9) 9)
    (hret : memLoad m (sp - 8) 64 = ret) (low : ret.toNat < 2^32) :
    ∃ (regs : Values Value Reg.count) (after : Ram), (program.sem (dialect code)).Reaches ⟨caller,[]⟩ ⟨⟨target,regs,after⟩,[]⟩ ∧
      regs[4] = ⟨64,sp⟩ ∧ regs[0] = ⟨64, ((args[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m after [⟨(sp-9).toNat,1⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        regs[i] = args[i] := by
  have sub9 : sp - 8 - 1 = sp - 9 := by bv_omega
  have stack1 : Writable code m (sp - 8 - 1) 1 := by
    rw [sub9]
    exact stack.sub (Nat.le_refl _) (by omega)
  have read : Readable m (sp - 8) 8 :=
    stack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨out,run,tag,rs,ra,frame,kept⟩ := K256.Proofs.Sec1.Serialize.choiceBlock
    (fun v hv => cover v (code_l127d50 v hv)) rsp stack1 read (hret ▸ low)
  have exec : program.Exec (dialect code) ⟨⟨.l127d50,args,m⟩,[]⟩ out :=
    .done (by simp only [Program.step, run, Transfer.next])
  refine ⟨out.values, out.store, Serialize.Coordinates.reaches_call step exec (hret ▸ tag),
    ?_, ra, sub9 ▸ frame, kept⟩
  simpa only [BitVec.sub_add_cancel] using rs

end K256.Proofs.Sec1.Affine.Uncompressed
