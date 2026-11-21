import K256.Proofs.Verify.Transfer.Compare
import K256.Proofs.Verify.Core.State
import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR

abbrev resumeAt (l : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64, ret⟩⟩

theorem reachesOfCall {code : CodeMap} {caller callee : Location Value Ram Label signature}
    {resume : Label} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (push : program.runBlock (dialect code) caller = .call callee (resumeAt resume ret))
    (run : program.Exec (dialect code) ⟨callee, []⟩ out) (tag : out.tag = some ⟨64, ret⟩) :
    (program.sem (dialect code)).Reaches ⟨caller, []⟩ ⟨⟨resume, out.values, out.store⟩, []⟩ := by
  refine .step (b := ⟨callee, [resumeAt resume ret]⟩) ?_ ?_
  · change (program.runBlock _ _).next _ _ = _
    rw [push]
    rfl
  · exact ParseSignature.exec_reaches_resume run _ [] (by rw [tag]; exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))

theorem resumeChoice {a b : Core.Registers} {m initial : Ram} {sp ret : BitVec 64}
    {l resume : Label}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l, a, initial⟩ =
      .call ⟨.l127d50, b, memStore m (sp - 8) ret⟩ (resumeAt resume ret))
    (rsp : b[4].get 64 = sp - 8) (work : Writable Extracted.programImage m (sp - 8 - 1) 1)
    (slot : Readable m (sp - 8) 8) (low : ret.toNat < 2^32) :
    ∃ c n, Core.Reaches l a initial resume c n ∧ c[4] = ⟨64, sp⟩ ∧
      c[0] = ⟨64, ((b[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame (memStore m (sp - 8) ret) n [⟨(sp - 8 - 1).toNat, 1⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        c[i] = b[i] := by
  have tag := memLoad_memStore_same m (sp - 8) ret (by decide) (by decide)
  obtain ⟨out, block, outTag, stack, flag, frame, kept⟩ := Sec1.Serialize.choiceBlock
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx))
    rsp (work.memStore _ ret) (slot.memStore _ ret) (tag ▸ low)
  have sec : Sec1.LIR.program.Exec (dialect Extracted.programImage)
      ⟨⟨.l127d50, b, memStore m (sp - 8) ret⟩, []⟩ out :=
    .done (by simp only [Program.step, block, CFG.Transfer.next])
  have gen : Generate.LIR.program.Exec (dialect Extracted.programImage)
      ⟨⟨.l127d50, b, memStore m (sp - 8) ret⟩, []⟩ out :=
    Generate.Serialize.Relabel.exec Generate.Serialize.matches_blocks sec rfl
  have run := Transfer.compareExec (dst := .l127d50) rfl gen
  exact ⟨_, _, reachesOfCall call run (tag ▸ outTag), by simpa only [BitVec.sub_add_cancel] using stack,
    flag, frame, kept⟩

end K256.Proofs.Verify
