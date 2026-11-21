import K256.Proofs.Signing.Composition.Attempt.Decode.Compare
import K256.Proofs.Signing.Composition.Attempt.Decode.AcceptBlocks
import K256.Proofs.Signing.Composition.Attempt.Decode.Choice

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private theorem choiceFrameOutside {s : RamState} {secret msg : ByteArray} {a : Registers} {m : Ram}
    {ret : BitVec 64} (call : ValidCall signingKeyTrySign s [secret,msg])
    {off : Nat} (fits : off+32 ≤ 1296) :
    Outside [(activation s m a 1 ret).region] (sp s+BitVec.ofNat 64 off) 32 := by
  have above := occursAboveCall (a:=a) (m:=m) (ret:=ret) (depth:=1) call (by decide)
    (off:=off) (size:=32) fits
  obtain ⟨room,_,base⟩ := stackBounds call
  have dst := offsetNat call (offset:=off) (by omega)
  have top : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have bottom : (sp s-8-1).toNat = (sp s).toNat-9 := by
    rw [show sp s-8-1 = sp s-9 by bv_omega]
    exact belowNat call (by decide)
  refine ⟨above.1,?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  right
  change (sp s-8-1).toNat + ((sp s-8).toNat-(sp s-8-1).toNat) ≤ _
  rw [bottom,top,dst]
  omega

private theorem afterPushWords {m : Ram} {base ret : BitVec 64} {off : Nat}
    {values : Vector (BitVec 64) 4} (source : WordsAt m (base+BitVec.ofNat 64 off) 64 values)
    (position : off = 128 ∨ off = 192) :
    WordsAt (memStore m (base-8) ret) (base+BitVec.ofNat 64 off) 64 values := by
  intro i hi
  refine (memLoad_memStore_of_rangeApart m _ _ _ 64 ?_).trans (source i hi)
  apply RangeApart.of_offsets (x:=base) (c:=0-8) (d:=BitVec.ofNat 64 (off+8*i))
  · exact addr_sub _ _
  · unfold wordAddr
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
  · have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases position with rfl | rfl <;> rcases index with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 900000 in
set_option maxRecDepth 4096 in
theorem invertChoice {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (checked : Selected s d msg st k a m) (zero : a[0].get 8 = 0) :
    ∃ b n, Reach (core .l10599c a m) (core .l1059a8 b n) ∧
      Selected s d msg st k b n ∧ b[0] = ⟨64,1⟩ := by
  let mem := memStore m (sp s-8) (0x1059a8 : BitVec 64)
  have spEq : a[4].get 64 = sp s := congrArg (Value.get 64) checked.rsp
  have low : (a[0].get 64).setWidth 8 = 0 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans zero
  have win : Writable Extracted.programImage m (sp s-8) 8 := by
    rw [addr_sub]
    exact stackWindow call checked.toMemory (by decide)
  obtain ⟨args,path,rsp,di,keep⟩ := invertChoiceBlock spEq low win
  have preserve (i : Fin Reg.count) (hi : i.val ∈ preservedRegisters) : args[i] = a[i] := by
    apply keep
    simp only [preservedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have widths : ParseSignature.ArgumentWidths args := by
    intro i hi
    by_cases h : i.val = 7
    · obtain ⟨j,jh⟩ := i
      change j = 7 at h
      subst j
      exact congrArg Value.width di
    · rw [keep i (by
        simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        omega)]
      exact checked.widths i hi
  have wrote := (RamWriteFrame.refl m _).memStore (0x1059a8 : BitVec 64) (returnSlot call)
  have stable := checked.toLoopMemory.preserve_work call wrote
  have slot : memLoad mem (sp s-8) 64 = (0x1059a8 : BitVec 64) :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have h14 : args[14].width = 64 :=
    (congrArg Value.width (keep 14 (by decide))).trans checked.r14
  obtain ⟨out,after,kept,regs,flag,r14,writes⟩ :=
    choice call stable checked.toRegistersAt path preserve rsp di h14 widths slot (by decide)
  have pushed : WordsAt mem (sp s+192) 64 (scalarWords k) :=
    afterPushWords checked.limbs (.inr rfl)
  have words := WordsAt.of_frame pushed writes (by decide) (choiceFrameOutside call (off:=192) (by decide))
  exact ⟨out.values,out.store,after,⟨kept,regs,words,
    (congrArg (Value.get 8) (r14.trans (keep 14 (by decide)))).trans checked.accepted⟩,flag⟩

set_option maxHeartbeats 950000 in
set_option maxRecDepth 4096 in
theorem accept {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (checked : Selected s d msg st k a m) (nonzero : a[0] = ⟨64,1⟩) :
    ∃ b n, Reach (core .l1059a8 a m) (core .l1059fb b n) ∧ NonceParsed s d msg st k b n := by
  let mem := memStore (copySelected m (sp s)) (sp s-8) (0x1059f3 : BitVec 64)
  have spEq : a[4].get 64 = sp s := congrArg (Value.get 64) checked.rsp
  have byte : (a[0].get 64).setWidth 8 = 1 := by rw [nonzero]; rfl
  have range : (a[14].get 64).setWidth 8 = 1 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans checked.accepted
  have win : Writable Extracted.programImage m (sp s-8) 232 := by
    rw [addr_sub]
    exact stackWindow call checked.toMemory (by decide)
  obtain ⟨args,path,rsp,di,keep,one,two⟩ := acceptCallBlock spEq byte range win
  have preserve (i : Fin Reg.count) (hi : i.val ∈ preservedRegisters) : args[i] = a[i] := by
    apply keep
    simp only [preservedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have widths : ParseSignature.ArgumentWidths args := by
    intro ⟨i,hi⟩ arg
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at arg
    rcases arg with rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width di
    · exact (congrArg Value.width (keep 6 (by decide))).trans (checked.widths 6 (by decide))
    · exact two
    · exact one
    · exact (congrArg Value.width (keep 8 (by decide))).trans (checked.widths 8 (by decide))
    · exact (congrArg Value.width (keep 9 (by decide))).trans (checked.widths 9 (by decide))
  have wrote := (copySelectedFrame (m:=m) call).memStore (0x1059f3 : BitVec 64) (returnSlot call)
  have stable := checked.toLoopMemory.preserve_work call wrote
  have slot : memLoad mem (sp s-8) 64 = (0x1059f3 : BitVec 64) :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have h14 : args[14].width = 64 :=
    (congrArg Value.width (keep 14 (by decide))).trans checked.r14
  obtain ⟨out,after,kept,regs,flag,_,writes⟩ :=
    choice call stable checked.toRegistersAt path preserve rsp di h14 widths slot (by decide)
  have pushed : WordsAt mem (sp s+128) 64 (scalarWords k) :=
    afterPushWords (copySelectedWords checked.limbs) (.inl rfl)
  have words := WordsAt.of_frame pushed writes (by decide) (choiceFrameOutside call (off:=128) (by decide))
  obtain ⟨b,branch,keeps⟩ := acceptBranch flag
  have jumped : Reach (core .l1059f3 out.values out.store) (core .l1059fb b out.store) :=
    .single (congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) branch)
  have postWidths : ParseSignature.ArgumentWidths b := by
    intro i hi
    rw [keeps i (by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact regs.widths i hi
  refine ⟨b,out.store,after.trans jumped,kept,⟨?_,?_,?_,?_,?_,?_,?_,?_,postWidths,?_⟩,words⟩
  · exact (keeps 4 (by decide)).trans regs.rsp
  · exact (keeps 22 (by decide)).trans regs.df
  · exact (keeps 3 (by decide)).trans regs.rbx
  · exact (keeps 5 (by decide)).trans regs.rbp
  · exact (keeps 12 (by decide)).trans regs.r12
  · exact (keeps 13 (by decide)).trans regs.r13
  · exact (congrArg Value.width (keeps 14 (by decide))).trans regs.r14
  · exact (keeps 15 (by decide)).trans regs.r15
  · exact ⟨(congrArg Value.width (keeps 39 (by decide))).trans regs.fp.1,
      (congrArg Value.width (keeps 50 (by decide))).trans regs.fp.2.1,
      (congrArg Value.width (keeps 51 (by decide))).trans regs.fp.2.2⟩

end K256.Proofs.Signing.Composition.Attempt.Decode
