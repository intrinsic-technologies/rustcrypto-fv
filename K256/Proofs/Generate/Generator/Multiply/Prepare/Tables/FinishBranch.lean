import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Blocks

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 900000 in
theorem finishBranch {q : BitVec 64} {m : Ram} {a : Registers}
    (win : Writable Extracted.programImage m q 3256) (high : q.toNat+3256 < 2^32)
    (rsp : a[4].get 64 = q) (df : a[22].get 1 = 0) (tmp : a[5].get 64 = q+1048)
    (work : a[15].get 64 = q+464) (index : a[14].get 64 = 0) (limit : memLoad m (q+104) 64 = 152)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a) :
    let n := memCopy (memCopy m (q+1048) (q+464) 120) (q+2008) (q+1048) 120
    ∃ (b : Registers), Reaches .l11d4e8 a m .l11d514 b n ∧ ParseSignature.ArgumentWidths b ∧
      SavedWidths b ∧ ∀ j : Fin Reg.count, j.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[j] = a[j] := by
  intro n
  have nLimit : memLoad n (q+104) 64 = 152 := by
    dsimp only [n,memCopy]
    repeat rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (x := q) rfl rfl (by decide))]
    exact limit
  dsimp only [n] at nLimit
  refine ⟨?out,?path,?w,?s,?regs⟩
  case path =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d4e8,a,m⟩ =
        .jump ⟨.l11d514,?out,n⟩ := by
      arithmetic_segment using code_l11d4e8 [rsp,df,tmp,work,index,limit,nLimit]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | rep_copy_guard using code_l11d4e8 | (dsimp only [memCopy]; slot_guard using code_l11d4e8))
      simp only [BitVec.reduceEq,ite_false]
      rfl
    exact Semantics.Reaches.single (by change program.step _ _ = _; simp only [Program.step,run,Transfer.next])
  case w =>
    rintro ⟨j,hj⟩ h
    have w := widths ⟨j,hj⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w
  case s =>
    rintro ⟨j,hj⟩ h
    have w := saved ⟨j,hj⟩ h
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact w
  case regs =>
    rintro ⟨j,hj⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
