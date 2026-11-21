import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Child
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Blocks
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Call

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private abbrev pushWrites (fr : Activation) : List MemoryRegion :=
  [⟨(roundSp fr - 8).toNat,8⟩]

abbrev windowCallWrites (fr : Activation) (dest : BitVec 64) : List MemoryRegion :=
  [⟨(roundSp fr - 0x220).toNat,0x220⟩,⟨(roundSp fr + dest).toNat,120⟩]

local macro "window_bounds" " using " e:term : tactic =>
  `(tactic| (
    have room := CoreEntry.room $e
    have high := CoreEntry.high $e
    simp (disch := decide) [tableOffset,windowCallWrites,pushWrites,roundWrites,roundSp,coreWrites,
      RegionsWithin,Outside,Activation.region,CoreEntry.low $e,
      Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,
      BitVec.reduceAdd,BitVec.reduceSub,CoreEntry.stackOffset $e,CoreEntry.aboveStack $e,
      BitVec.reduceToNat] <;> omega))

private theorem roundPush (fr : Activation) (m : Ram) (tag : BitVec 64) (low : (roundSp fr - 8).toNat + 8 ≤ 2^64) :
    RamWriteFrame m (memStore m (roundSp fr - 8) tag) (pushWrites fr) :=
  (RamWriteFrame.refl m _).memStore tag ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,low⟩

private theorem roundStack {fr : Activation} {a : Registers} {m : Ram} {d k : Nat} {site : Label}
    (s : RoundState fr d k site a m) (layout : Fn11c880.frameAt site fr = Fn11c880.frameAt .l11d7d0 fr) :
    Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8 := by
  have h := s.atoms
  rw [layout] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem WindowCall.resume {fr : Activation} {a b initial : Registers} {m : Ram} {d k : Nat}
    {site child resume : Label} {tag : BitVec 64} {out : Output Value Ram Reg.count}
    (entry : CoreEntry fr initial d) (s : RoundState fr d k site a m)
    (sourceAt : Fn11c880.frameAt site fr = Fn11c880.frameAt .l11d7d0 fr)
    (targetAt : Fn11c880.frameAt resume fr = Fn11c880.frameAt .l11d7d0 fr)
    (c : WindowCall fr site child resume tag a b m)
    (exec : program.Exec (dialect Extracted.programImage) ⟨⟨child,b,memStore m (roundSp fr - 8) tag⟩, []⟩ out)
    (ret : out.tag = some ⟨64,tag⟩)
    (done_ : Atom.All Extracted.programImage out.values out.store
      (Fn10a410.doneAt (windowChild fr b (memStore m (roundSp fr - 8) tag) tag)))
    (widths : ParseSignature.ArgumentWidths out.values)
    {writes : List MemoryRegion} (frame : RamWriteFrame (memStore m (roundSp fr - 8) tag) out.store writes)
    (within : RegionsWithin writes (roundWrites (roundSp fr))) :
    Reaches site a m resume out.values out.store ∧ RoundState fr d k resume out.values out.store ∧
    ∀ j : Fin Reg.count, j.val ∈ Activation.calleeSavedNumbers → out.values[j] = b[j] := by
  obtain ⟨path,saved,rsp,ctrl,keep⟩ := c.returned s sourceAt exec ret done_
  have atoms := s.atoms
  rw [sourceAt] at atoms
  have oldsp : a[4] = ⟨64,roundSp fr⟩ := atoms.1
  have push := roundPush fr m tag (by window_bounds using entry)
  refine ⟨path,RoundState.afterWrites entry s sourceAt targetAt ?_ ?_ widths saved,keep⟩
  · exact ((RamWriteFrame.refl _ _).trans push (by window_bounds using entry)).trans frame within
  · intro j hj
    rcases List.mem_cons.mp hj with h | h
    · have : j = 4 := Fin.ext h
      subst j
      exact rsp.trans oldsp.symm
    · exact ctrl j h

theorem windowLookup (select : type_of% @lookup) (first : Bool) {fr : Activation} {initial a : Registers}
    {m : Ram} {d k : Nat} {p : Projective} (entry : CoreEntry fr initial d) (bound : k < 32)
    (s : RoundState fr d k (lookupSite first) a m)
    (acc : p.Stored m (roundSp fr + 0x128))
    (table : TableAt m (roundSp fr + tableOffset first) (windowBase first d))
    (temp : a[12].get 64 = roundSp fr + tableOffset first) (zero : a[14].get 64 = 0)
    (ptr : first = false → a[13].get 64 = digitPointer fr k)
    (dst : first = false → a[5].get 64 = roundSp fr + 0x1d0) :
    ∃ b n, ∃ l : Projective, Reaches (lookupSite first) a m (lookupResume first) b n ∧
      RoundState fr d k (lookupResume first) b n ∧ p.Stored n (roundSp fr + 0x128) ∧
      l.Stored n (roundSp fr + 0x1d0) ∧ l.valid ∧ l.value = Curve.selectDigit (windowBase first d) (windowIndex first d k) ∧
      b[5].get 64 = roundSp fr + 0x1d0 ∧ b[12].get 64 = roundSp fr + 0x490 ∧
      b[13].get 64 = digitPointer fr k ∧ b[14].get 64 = 0 ∧ b[15] = a[15] ∧
      RamWriteFrame m n (windowCallWrites fr 0x1d0) := by
  obtain ⟨b,c,di,si,dx,bp,r12,r13,r14,r15⟩ := windowLookupBlock first entry bound s temp zero ptr dst
  let tag := lookupTag first
  let n := memStore m (roundSp fr - 8) tag
  let f := windowChild fr b n tag
  have sourceAt : Fn11c880.frameAt (lookupSite first) fr = Fn11c880.frameAt .l11d7d0 fr := by cases first <;> rfl
  have targetAt : Fn11c880.frameAt (lookupResume first) fr = Fn11c880.frameAt .l11d7d0 fr := by cases first <;> rfl
  have atChild : Atom.All Extracted.programImage b n (Fn11c510.frameAt .l11c510 f) :=
    c.entry entry s sourceAt Fn11c510.frameInfo rfl (by decide) (by decide) (by cases first <;> decide)
  have src : f.rsi = roundSp fr + tableOffset first := si
  have dest : f.rdi = roundSp fr + 0x1d0 := di
  have sp : f.rsp = roundSp fr - 8 := rfl
  have stack := (roundStack s sourceAt).memStore (roundSp fr - 8) tag
  have push := roundPush fr m tag (by window_bounds using entry)
  have table' := table.of_frame push (by cases first <;> window_bounds using entry)
  obtain ⟨lo,hi⟩ := Curve.radixDigit_bounds (Curve.radixRemaining (windowComponent first d).natAbs k)
  obtain ⟨out,l,exec,ret,done_,widths,lv,stored,value,frame⟩ := select atChild
    (entry.loaded_of_frame (s.memory.frame.trans push (by window_bounds using entry)))
    (by rw [src]; apply stack.readable.sub <;> cases first <;> window_bounds using entry)
    (by rw [dest]; apply stack.sub <;> window_bounds using entry)
    (by rw [sp,src]; cases first <;> window_bounds using entry)
    (by rw [sp,dest]; window_bounds using entry)
    (by rw [src,dest]; cases first <;> window_bounds using entry) (src ▸ table')
    ⟨lo,Int.le_trans hi (by decide)⟩ dx
  rw [sp,dest] at frame
  rw [dest] at stored
  obtain ⟨path,state,keep⟩ := c.resume entry s sourceAt targetAt exec ret done_ widths frame (by window_bounds using entry)
  have full : RamWriteFrame m out.store (windowCallWrites fr 0x1d0) :=
    ((RamWriteFrame.refl _ _).trans push (by window_bounds using entry)).trans frame (by window_bounds using entry)
  have eq (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :=
    congrArg (Value.get 64) (keep i hi)
  exact ⟨_,_,l,path,state,acc.of_frame full (by window_bounds using entry),stored,lv,value,
    (eq 5 (by decide)).trans bp,(eq 12 (by decide)).trans r12,(eq 13 (by decide)).trans r13,
    (eq 14 (by decide)).trans r14,(keep 15 (by decide)).trans r15,full⟩

theorem windowAddition (add : type_of% @addCall) (first : Bool) {fr : Activation} {initial a : Registers}
    {m : Ram} {d k : Nat} {p l : Projective} (entry : CoreEntry fr initial d)
    (s : RoundState fr d k (lookupResume first) a m)
    (left : p.Stored m (roundSp fr + 0x128)) (right : l.Stored m (roundSp fr + 0x1d0))
    (dst : a[5].get 64 = roundSp fr + 0x1d0) (acc : first = false → a[15].get 64 = roundSp fr + 0x128) :
    ∃ b n, Reaches (lookupResume first) a m (additionResume first) b n ∧
      RoundState fr d k (additionResume first) b n ∧ (p.add l).Stored n (roundSp fr + 0x128) ∧
      b[15].get 64 = roundSp fr + 0x128 ∧ (∀ j : Fin Reg.count, j.val ∈ [5,12,13,14] → b[j] = a[j]) ∧
      RamWriteFrame m n (windowCallWrites fr 0x128) := by
  obtain ⟨b,c,di,si,r15,regs⟩ := windowAdditionBlock first s dst acc
  let tag := additionTag first
  let n := memStore m (roundSp fr - 8) tag
  let f := windowChild fr b n tag
  have sourceAt : Fn11c880.frameAt (lookupResume first) fr = Fn11c880.frameAt .l11d7d0 fr := by cases first <;> rfl
  have targetAt : Fn11c880.frameAt (additionResume first) fr = Fn11c880.frameAt .l11d7d0 fr := by cases first <;> rfl
  have atChild : Atom.All Extracted.programImage b n (Fn10a410.frameAt .l10a410 f) :=
    c.entry entry s sourceAt Fn10a410.frameInfo rfl (by decide) (by decide) (by cases first <;> decide)
  have src : f.rsi = roundSp fr + 0x1d0 := si
  have dest : f.rdi = roundSp fr + 0x128 := di
  have sp : f.rsp = roundSp fr - 8 := rfl
  have stack := (roundStack s sourceAt).memStore (roundSp fr - 8) tag
  have push := roundPush fr m tag (by window_bounds using entry)
  obtain ⟨out,exec,ret,done_,widths,value,frame⟩ := add Common.fnCode_subset_programImage f b n p l atChild
    (by rw [src]; apply stack.readable.sub <;> window_bounds using entry)
    (by rw [dest]; apply stack.sub <;> window_bounds using entry)
    (by rw [sp,src]; window_bounds using entry)
    (by rw [sp,dest]; window_bounds using entry)
    (by rw [src,dest]; window_bounds using entry)
    (dest ▸ left.of_frame push (by window_bounds using entry)) (src ▸ right.of_frame push (by window_bounds using entry))
  rw [sp,dest] at frame
  rw [dest] at value
  obtain ⟨path,state,keep⟩ := c.resume entry s sourceAt targetAt exec ret done_ widths frame (by window_bounds using entry)
  refine ⟨_,_,path,state,value,(congrArg (Value.get 64) (keep 15 (by decide))).trans r15,?_,?_⟩
  · intro j hj
    exact (keep j (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj ⊢; omega)).trans (regs j hj)
  · exact ((RamWriteFrame.refl _ _).trans push (by window_bounds using entry)).trans frame (by window_bounds using entry)

theorem rightTableAfterCalls {fr : Activation} {initial : Registers} {d : Nat} {m n o : Ram}
    (entry : CoreEntry fr initial d) (table : TableAt m (roundSp fr + 0x490) (secondBase d))
    (lookupFrame : RamWriteFrame m n (windowCallWrites fr 0x1d0)) (additionFrame : RamWriteFrame n o (windowCallWrites fr 0x128)) :
    TableAt o (roundSp fr + 0x490) (secondBase d) :=
  (table.of_frame lookupFrame (by window_bounds using entry)).of_frame additionFrame (by window_bounds using entry)

end K256.Proofs.Generate.Generator.Multiply
