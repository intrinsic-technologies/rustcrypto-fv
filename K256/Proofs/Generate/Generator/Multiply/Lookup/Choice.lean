import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag
import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Sec1.Serialize.Choice

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field

theorem resumeChoice {l next : Label} {a b : Registers} {initial m : Ram} {sp ret : Word}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l, a, initial⟩ =
      .call ⟨.l127d50, b, memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (tmp : Writable Extracted.programImage m (sp - 8 - 1) 1)
    (slot : Readable m (sp - 8) 8) (low : ret.toNat < 2^32) :
    ∃ c n, Reaches l a initial next c n ∧ c[4] = ⟨64,sp⟩ ∧
      c[0] = ⟨64, ((b[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame (memStore m (sp - 8) ret) n [⟨(sp - 8 - 1).toNat,1⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] → c[i] = b[i] := by
  have tag := memLoad_memStore_same m (sp - 8) ret (by decide) (by decide)
  obtain ⟨out, block, outTag, stack, flag, frame, kept⟩ := Sec1.Serialize.choiceBlock
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx))
    rsp (tmp.memStore _ ret) (slot.memStore _ ret) (tag ▸ low)
  have sec : Sec1.LIR.program.Exec (dialect Extracted.programImage)
      ⟨⟨.l127d50, b, memStore m (sp - 8) ret⟩, []⟩ out :=
    .done (by simp only [Program.step, block, Transfer.next])
  have run : program.Exec (dialect Extracted.programImage)
      ⟨⟨.l127d50, b, memStore m (sp - 8) ret⟩, []⟩ out :=
    Serialize.Relabel.exec Serialize.matches_blocks sec rfl
  refine ⟨out.values, out.store, Sample.reachesAfterSampleCall call run (tag ▸ outTag) [], ?_, flag, frame, kept⟩
  simpa only [BitVec.sub_add_cancel] using stack

end K256.Proofs.Generate.Generator.Multiply.Lookup
