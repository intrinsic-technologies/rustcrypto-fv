import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply.Split.Caller (Site)

theorem ChildRegs.savedWidths {site : Site} {a c : Registers} {sp scalar tables : BitVec 64}
    (regs : ChildRegs site a sp scalar tables c) :
    ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64 := by
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  exact congrArg Value.width regs.bx
  exact congrArg Value.width regs.bpReg
  exact congrArg Value.width regs.scalarReg
  exact congrArg Value.width regs.r13Reg
  exact regs.r14Width
  exact congrArg Value.width regs.r15Reg

theorem ChildRegs.entry {site : Site} {a c : Registers} {m n : Ram} {sp scalar tables : BitVec 64}
    (regs : ChildRegs site a sp scalar tables c) (entry : RoutineEntry a m sp 0x558)
    (whole : RamWriteFrame m n [scratch sp 0x558]) (tag : memLoad n (frameSp sp - 8) 64 = ret site) :
    RoutineEntry c n (frameSp sp - 8) site.window := by
  obtain ⟨_,hw,_⟩ := bounds site
  have win := entry.stack.of_frame whole
  refine ⟨regs.rsp,regs.savedWidths,(regs.ctrl 22 (by decide)).trans entry.df,
    (congrArg Value.width (regs.ctrl 39 (by decide))).trans entry.mxcsr,
    (congrArg Value.width (regs.ctrl 50 (by decide))).trans entry.ftw,
    (congrArg Value.width (regs.ctrl 51 (by decide))).trans entry.fcw,?_,?_,?_,?_,?_,
    Recode.imageFromFrame entry whole⟩
  · have align := entry.aligned
    split_bounds entry
  · split_bounds entry
  · exact win.sub (by split_bounds entry) (by split_bounds entry)
  · exact win.readable.sub (by split_bounds entry) (by split_bounds entry)
  · rw [tag]
    cases site <;> decide

theorem afterReturn (site : Site) {a b c : Registers} {m n pushed : Ram}
    {sp src scalar tables digits : BitVec 64} {out : Output Value Ram Reg.count}
    (entry : RoutineEntry a m sp 0x558) (prev : SplitFrame a m sp src tables digits b n)
    (regs : ChildRegs site a sp scalar tables c)
    (push : RamWriteFrame n pushed (writes sp site))
    (post : RoutineReturn c pushed (frameSp sp - 8) site.window
      [⟨(slot sp (destination site)).toNat,32⟩] out)
    (args : ParseSignature.ArgumentWidths out.values) :
    Returned site a m sp src scalar tables digits out.values out.store := by
  have foot := push.trans post.frame (callWithin entry site)
  obtain ⟨_,_,destHi,dd,dl⟩ := bounds site
  have saved (i : BitVec 64) (lo : 8 ≤ i.toNat) (hi : i.toNat ≤ 48) :
      memLoad out.store (sp-i) 64 = memLoad n (sp-i) 64 := by
    apply foot.memLoad_eq
    refine ⟨by split_bounds entry,fun r hr => ?_⟩
    simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> split_bounds entry
  have p := foot.memLoad_eq (k := 64) (outsideLocal entry site 40 8 (by decide) (Or.inl dl))
  have d := foot.memLoad_eq (k := 64) (outsideLocal entry site 216 8 (by decide) dd.symm)
  refine ⟨⟨⟨post.rsp.trans (by rw [BitVec.sub_add_cancel]),(post.saved 3 (by decide)).trans regs.bx,
      ?_,?_,(saved 48 (by decide) (by decide)).trans prev.rbx,(saved 40 (by decide) (by decide)).trans prev.r12,
      (saved 32 (by decide) (by decide)).trans prev.r13,(saved 24 (by decide) (by decide)).trans prev.r14,
      (saved 16 (by decide) (by decide)).trans prev.r15,(saved 8 (by decide) (by decide)).trans prev.rbp⟩,
      prev.frame.trans foot (writesWithin entry site),p.trans prev.pointPtr,d.trans prev.digitPtr,args⟩,
      (post.saved 5 (by decide)).trans regs.bpReg,(post.saved 12 (by decide)).trans regs.scalarReg,
      (post.saved 13 (by decide)).trans regs.r13Reg,(post.saved 15 (by decide)).trans regs.r15Reg⟩
  · intro i hi
    exact (congrArg Value.width (post.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans
      (regs.savedWidths i hi)
  · intro i hi
    exact (post.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (regs.ctrl i hi)

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
