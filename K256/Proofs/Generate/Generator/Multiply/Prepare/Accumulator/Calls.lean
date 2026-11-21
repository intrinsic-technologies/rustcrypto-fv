import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.TableCopy
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Return
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Call

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def callWrites (fr : Activation) (dst : BitVec 64) (len : Nat) : List MemoryRegion :=
  [⟨(sp fr - 544).toNat,544⟩,⟨(sp fr + dst).toNat,len⟩]

abbrev tableSource (fr : Activation) (first : Bool) := if first then fr.rcx else fr.rcx + 960

theorem copyCall (first : Bool) {fr : Activation} {a b initial : Registers} {m : Ram} {d : Nat}
    {l r : Label} {tag : BitVec 64} {p : Standards.SECG.ECC.Curve.Point}
    (entry : CoreEntry fr initial d) (s : State l fr a m)
    (old : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (next : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr l .l12a820 r tag a b m) (small : tag.toNat < 2^32)
    (di : b[7].get 64 = sp fr + tableOffset first) (si : b[6].get 64 = tableSource fr first)
    (dx : b[2].get 64 = 960) (tab : TableAt m (tableSource fr first) p) :
    ∃ v n, Reaches l a m r v n ∧ State r fr v n ∧ TableAt n (sp fr + tableOffset first) p ∧
      RamWriteFrame m n (callWrites fr (tableOffset first) 960) ∧
      ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → v[i] = b[i] := by
  let src := tableSource fr first
  let dst := sp fr + tableOffset first
  let pMem := memStore m (sp fr - 8) tag
  let n := memCopy pMem dst src 960
  have fPush := pushFrame entry m tag
  obtain ⟨_,df,stack⟩ := currentStack s old
  have wr : Writable Extracted.programImage pMem dst 960 := by
    apply (stack.memStore (sp fr - 8) tag).sub <;> cases first <;> dsimp only [dst,tableOffset] <;> acc_bounds using entry
  have ext := entry.tableWrite.of_frame (s.frame.trans fPush (by acc_bounds using entry))
  have rd : Readable pMem src 960 := by
    apply ext.readable.sub <;> cases first <;> dsimp only [src,tableSource] <;> acc_bounds using entry
  have safe : Outside (pushWrites fr) src 960 := by cases first <;> dsimp only [src,tableSource] <;> acc_bounds using entry
  have align : dst.toNat % 8 = 0 := by
    have h := s.atoms
    rw [old] at h
    have aligned : fr.rsp.toNat % 16 = 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cases first <;> dsimp only [dst,tableOffset] <;> acc_bounds using entry
  have fCopy : RamWriteFrame pMem n [⟨dst.toNat,960⟩] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by have := wr.readable.low; omega⟩
  have f : RamWriteFrame m n (callWrites fr (tableOffset first) 960) := by
    apply ((RamWriteFrame.refl _ _).trans fPush ?_).trans fCopy
    all_goals cases first <;> dsimp only [callWrites,dst,tableOffset] <;> acc_bounds using entry
  have savedTag : memLoad n (sp fr - 8) 64 = tag :=
    (fCopy.memLoad_eq (by cases first <;> dsimp only [dst,tableOffset] <;> acc_bounds using entry)).trans
      (memLoad_memStore_same _ _ _ (by decide) (by decide))
  have slot : Readable pMem (sp fr - 8) 8 := by
    apply (stack.memStore (sp fr - 8) tag).readable.sub <;> acc_bounds using entry
  obtain ⟨out,exec,ret,mem,args,back,keep⟩ := copyTable di si dx (congrArg (Value.get 64) c.rsp)
    (congrArg (Value.get 1) ((c.control 22 (by decide)).trans df)) align c.widths rd wr
    (by cases first <;> dsimp only [src,dst,tableSource,tableOffset] <;> acc_bounds using entry)
    (LoadOk.of_region (slot.of_frame fCopy) (Nat.le_refl _) (Nat.le_refl _)) savedTag small
  have path := Sample.reachesAfterSampleCall c.step exec ret []
  change out.store = n at mem
  rw [mem] at path
  exact ⟨_,n,path,resumeState entry s old next c ((RamWriteFrame.refl _ _).trans f
    (by cases first <;> dsimp only [callWrites,tableOffset] <;> acc_bounds using entry))
    args (by change out.values[4] = ⟨64,sp fr - 8 + 8⟩ at back; simpa only [BitVec.sub_add_cancel] using back) keep,(tab.of_frame fPush safe).memCopy,f,keep⟩

theorem pointLookup (select : type_of% @lookup) (first : Bool) {fr : Activation} {a b initial : Registers}
    {m : Ram} {d : Nat} {l r : Label} {tag : BitVec 64} {p : Standards.SECG.ECC.Curve.Point} {digit : Int}
    (entry : CoreEntry fr initial d) (s : State l fr a m)
    (old : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (next : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr l .l11c510 r tag a b m) (small : tag.toNat < 2^32)
    (di : b[7].get 64 = sp fr + 0x1d0) (si : b[6].get 64 = sp fr + tableOffset first)
    (dx : (b[2].get 64).setWidth 8 = BitVec.ofInt 8 digit) (lim : -8 ≤ digit ∧ digit ≤ 8)
    (tab : TableAt m (sp fr + tableOffset first) p) :
    ∃ v n, ∃ t : Projective, Reaches l a m r v n ∧ State r fr v n ∧ t.valid ∧
      t.Stored n (sp fr + 0x1d0) ∧ t.value = Curve.selectDigit p digit ∧
      RamWriteFrame m n (callWrites fr 0x1d0 120) ∧
      ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → v[i] = b[i] := by
  let pm := memStore m (sp fr - 8) tag
  let ch := child fr b pm tag
  have childAtoms : Atom.All Extracted.programImage b pm (Fn11c510.frameAt .l11c510 ch) :=
    enter entry s old c Fn11c510.frameInfo rfl (by decide) small
  have src : ch.rsi = sp fr + tableOffset first := si
  have dst : ch.rdi = sp fr + 0x1d0 := di
  have rsp : ch.rsp = sp fr - 8 := rfl
  have stack := (currentStack s old).2.2.memStore (sp fr - 8) tag
  have push := pushFrame entry m tag
  obtain ⟨out,t,exec,ret,done_,args,valid,stored,val,written⟩ := select childAtoms
    (entry.loaded_of_frame (s.frame.trans push (by acc_bounds using entry)))
    (by rw [src]; apply stack.readable.sub <;> cases first <;> dsimp only [tableOffset] <;> acc_bounds using entry)
    (by rw [dst]; apply stack.sub <;> acc_bounds using entry)
    (by rw [rsp,src]; cases first <;> dsimp only [tableOffset] <;> acc_bounds using entry)
    (by rw [rsp,dst]; acc_bounds using entry)
    (by rw [dst,src]; cases first <;> dsimp only [tableOffset] <;> acc_bounds using entry)
    (src ▸ tab.of_frame push (by cases first <;> dsimp only [tableOffset] <;> acc_bounds using entry)) lim dx
  rw [rsp,dst] at written
  have full : RamWriteFrame m out.store (callWrites fr 0x1d0 120) :=
    ((RamWriteFrame.refl _ _).trans push (by dsimp only [callWrites]; acc_bounds using entry)).trans written
      (by dsimp only [callWrites]; acc_bounds using entry)
  obtain ⟨back,keep⟩ := returned s old c done_
  exact ⟨_,_,t,Sample.reachesAfterSampleCall c.step exec ret [],resumeState entry s old next c
    ((RamWriteFrame.refl _ _).trans full (by dsimp only [callWrites]; acc_bounds using entry)) args back keep,
    valid,dst ▸ stored,val,full,keep⟩

theorem pointAdd (add : type_of% @addCall) {fr : Activation} {a b initial : Registers} {m : Ram}
    {d : Nat} {l r : Label} {tag : BitVec 64} {p q : Projective}
    (entry : CoreEntry fr initial d) (s : State l fr a m)
    (old : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (next : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr l .l10a410 r tag a b m) (small : tag.toNat < 2^32)
    (di : b[7].get 64 = sp fr + 0x128) (si : b[6].get 64 = sp fr + 0x1d0)
    (left : p.Stored m (sp fr + 0x128)) (right : q.Stored m (sp fr + 0x1d0)) :
    ∃ v n, Reaches l a m r v n ∧ State r fr v n ∧ (p.add q).Stored n (sp fr + 0x128) ∧
      RamWriteFrame m n (callWrites fr 0x128 120) ∧
      ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → v[i] = b[i] := by
  let pm := memStore m (sp fr - 8) tag
  let ch := child fr b pm tag
  have childAtoms : Atom.All Extracted.programImage b pm (Fn10a410.frameAt .l10a410 ch) :=
    enter entry s old c Fn10a410.frameInfo rfl (by decide) small
  have src : ch.rsi = sp fr + 0x1d0 := si
  have dst : ch.rdi = sp fr + 0x128 := di
  have rsp : ch.rsp = sp fr - 8 := rfl
  have stack := (currentStack s old).2.2.memStore (sp fr - 8) tag
  have push := pushFrame entry m tag
  obtain ⟨out,exec,ret,done_,args,stored,written⟩ := add Common.fnCode_subset_programImage ch b pm p q childAtoms
    (by rw [src]; apply stack.readable.sub <;> acc_bounds using entry)
    (by rw [dst]; apply stack.sub <;> acc_bounds using entry)
    (by rw [rsp,src]; acc_bounds using entry) (by rw [rsp,dst]; acc_bounds using entry)
    (by rw [dst,src]; acc_bounds using entry)
    (dst ▸ left.of_frame push (by acc_bounds using entry)) (src ▸ right.of_frame push (by acc_bounds using entry))
  rw [rsp,dst] at written
  have full : RamWriteFrame m out.store (callWrites fr 0x128 120) :=
    ((RamWriteFrame.refl _ _).trans push (by dsimp only [callWrites]; acc_bounds using entry)).trans written
      (by dsimp only [callWrites]; acc_bounds using entry)
  obtain ⟨back,keep⟩ := returned s old c done_
  exact ⟨_,_,Sample.reachesAfterSampleCall c.step exec ret [],resumeState entry s old next c
    ((RamWriteFrame.refl _ _).trans full (by dsimp only [callWrites]; acc_bounds using entry)) args back keep,
    dst ▸ stored,full,keep⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
