import K256.Proofs.Verify.Core.Lincomb.Recode.Frame
import K256.Proofs.Verify.Core.Lincomb.Recode.Advance
import K256.Proofs.Verify.Core.Lincomb.Recode.Padding
import K256.Proofs.Verify.Core.Lincomb.Recode.FinalDigit
import K256.Proofs.Verify.Core.Lincomb.Recode.Entry
import K256.Proofs.Verify.Core.Lincomb.Recode.Initialize

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

structure MemoryContext (a : Registers) (m : Ram) (sp dst : BitVec 64) : Prop where
  entry : RoutineEntry a m sp 0x110
  buffer : Writable Extracted.programImage m dst 257
  separate : Outside [scratch sp 0x110, ⟨sp.toNat,8⟩] dst 257

structure LoopState (a b : Registers) (initial current : Ram) (sp dst next lo hi : BitVec 64)
    (i c previous : Nat) (ds : List Int) : Prop where
  registers : LoopRegisters a b sp i c
  frame : RamWriteFrame initial current (writes sp dst)
  saved : SavedAt a sp current
  fields : LoopMemory current sp dst
  iterator : IteratorAt current (sp-88) next previous
    (if previous = 0 then lo else hi) (if previous = 0 then hi else 0)
  bytes : DigitBytes current dst ds
  index : ds.length = i
  carry : c ≤ 1
  cached : previous ≤ i/64 ∧ i/64 ≤ previous+1

private theorem outsideWithin {r s : List MemoryRegion} {a : BitVec 64} {len : Nat}
    (outside : Outside s a len) (subset : RegionsWithin r s) : Outside r a len := by
  refine ⟨outside.1, fun reg hr => ?_⟩
  obtain ⟨big, hb, lower, upper⟩ := subset reg hr
  rcases outside.2 big hb with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem outsideScratch {sp dst : BitVec 64}
    (separate : Outside [scratch sp 0x110, ⟨sp.toNat,8⟩] dst 257) :
    Outside [scratch sp 0x110] dst 257 :=
  ⟨separate.1, fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact separate.2 _ List.mem_cons_self⟩

private theorem stackRead {a : Registers} {orig m : Ram} {sp dst off : BitVec 64} {len : Nat}
    (ctx : MemoryContext a orig sp dst) (frame : RamWriteFrame orig m (writes sp dst))
    (fit : off.toNat ≤ 0x110) (top : len ≤ off.toNat) : LoadOk m (sp-off) len :=
  let readable := ((stackSlot ctx.entry fit top).of_frame frame).readable
  ⟨readable.low,readable.present⟩

private theorem preserveWrite {a : Registers} {orig m n : Ram} {sp dst next lo hi : BitVec 64} {j : Nat}
    (ctx : MemoryContext a orig sp dst) (frame : RamWriteFrame m n [⟨dst.toNat,257⟩])
    (saved : SavedAt a sp m) (fields : LoopMemory m sp dst) (iter : IteratorAt m (sp-88) next j lo hi) :
    SavedAt a sp n ∧ LoopMemory n sp dst ∧ IteratorAt n (sp-88) next j lo hi := by
  have slot {off : BitVec 64} {len : Nat} (fit : off.toNat ≤ 0x110) (top : len ≤ off.toNat) :=
    slotOutsideDigits ctx.entry.room ctx.entry.returnSlot.low fit top ctx.separate
  refine ⟨saved.of_frame frame (fun _ l u => slot (by omega) l),
    fields.of_frame frame (fun _ _ _ l u => slot (by omega) (by omega)), ?_⟩
  exact WordsAt.of_frame iter frame (by decide) (slot (off := 88) (by decide) (by decide))

set_option maxHeartbeats 600000 in
private theorem readAndClassify {a b : Registers} {orig m : Ram} {sp dst next lo hi : BitVec 64}
    {i c previous : Nat} {ds : List Int}
    (ctx : MemoryContext a orig sp dst) (st : LoopState a b orig m sp dst next lo hi i c previous ds)
    (bound : i < 128) :
    let w := (((hi ++ lo).toNat / 2^i) % (32 : Nat)) + c
    ∃ (r : Registers) (n : Ram),
      Continues .l110847 b m (if w % 2 = 0 then .l11089f else .l1108d0) r n ∧
      LoopState a r orig n sp dst next lo hi i c (i/64) ds ∧
      r[2].get 64 = BitVec.ofNat 64 w ∧ r[6] = ⟨64,dst⟩ := by
  let pushed := pushRead m sp
  have room := ctx.entry.room
  have low := ctx.entry.returnSlot.low
  have pushArea := stackSlot ctx.entry (off := 144) (by decide) (by decide : 8 ≤ (144 : BitVec 64).toNat)
  have callOk : StoreOk Extracted.programImage m (sp-144) 8 0x110859 5 :=
    storeGuard (off := 18) (pushArea.of_frame st.frame) code_l110847 (by decide)
  obtain ⟨args,call,arguments⟩ := callRead st.registers bound callOk
  let pushRegion : MemoryRegion := ⟨(sp-144).toNat,8⟩
  have pushFrame : RamWriteFrame m pushed [pushRegion] :=
    (RamWriteFrame.refl m _).memStore _ ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,
      by have := pushArea.readable.low; omega⟩
  have pushedFrame : RamWriteFrame orig pushed (writes sp dst) := by
    apply st.frame.trans pushFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have h := inScratch (sp := sp) room (off := 144) (len := 8) (by decide) (by decide)
    exact ⟨_, List.mem_cons_self, h.1, h.2.1⟩
  have pushAside {off : BitVec 64} {l : Nat} (h : off.toNat ≤ 136) (len : l ≤ off.toNat) :
      Outside [pushRegion] (sp-off) l := by
    refine ⟨by rw [subNat (by omega)]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp-144).toNat + 8 ≤ (sp-off).toNat
    have z : (sp-144).toNat = sp.toNat-144 := subNatConst (sp := sp) (k := 144) (by omega)
    rw [z, subNat (by omega : off.toNat ≤ sp.toNat)]
    omega
  have savedWidths : ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15] → args[j].width = 64 := by
    intro ⟨j, hj⟩ live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at live
    rcases live with rfl | rfl | rfl | rfl | rfl | rfl
    · change args[3].width = 64
      rw [arguments.offset]
    · change args[5].width = 64
      rw [arguments.offsetNeg, st.registers.negIndex]
    · change args[12].width = 64
      rw [arguments.width, st.registers.width]
    · change args[13].width = 64
      rw [arguments.carry, st.registers.carry]
    · change args[14].width = 64
      rw [arguments.length, st.registers.length]
    · change args[15].width = 64
      rw [arguments.bitIndex, st.registers.bitIndex]
  have retAt : memLoad pushed (sp-144) 64 = 0x11085e := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have childEntry := iteratorEntry ctx.entry ctx.buffer pushedFrame arguments.rsp savedWidths
    arguments.saved retAt (by decide)
  have it : IteratorAt pushed (sp-88) next previous
      (if previous = 0 then lo else hi) (if previous = 0 then hi else 0) :=
    WordsAt.of_frame st.iterator pushFrame (by decide) (pushAside (off := 88) (by decide) (by decide))
  have slot := stackSlot ctx.entry (off := 88) (by decide) (by decide : 40 ≤ (88 : BitVec 64).toNat)
  obtain ⟨out,exe,ret,ax,dx,it'⟩ :=
    advanceIterator childEntry arguments.iterator arguments.wordIndex st.cached.1 st.cached.2
      (by omega : i/64 ≤ 1) it (slot.of_frame pushedFrame) (bufferSeparate room low)
  let q := out.store
  have unchanged {off : BitVec 64} {l : Nat} (h : off.toNat ≤ 136) (h' : l ≤ off.toNat)
      (gap : 88+l ≤ off.toNat ∨ off.toNat ≤ 48) :
      Outside [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] (sp-off) l :=
    skipChildWrites room low h h' gap
  have fields := (st.fields.of_frame pushFrame (fun _ _ _ l h => pushAside h (by omega))).of_frame
    ret.frame (fun _ _ _ l h => unchanged h (by omega) (Or.inl l))
  have saved := (st.saved.of_frame pushFrame (fun _ l h => pushAside (by omega) l)).of_frame
    ret.frame (fun _ l h => unchanged (by omega) l (Or.inr h))
  have frame := pushedFrame.trans ret.frame (childWrites room)
  have pushedZeros : DigitBytes pushed dst ds := by
    apply digitBytes_of_frame pushFrame ?_ st.bytes
    apply outsideWithin (outsideScratch ctx.separate)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have h := inScratch (sp := sp) room (off := 144) (len := 8) (by decide) (by decide)
    exact ⟨_,List.mem_singleton_self _,h.1,h.2.1⟩
  have bytes : DigitBytes q dst ds :=
    digitBytes_of_frame ret.frame (outsideWithin (outsideScratch ctx.separate) (childInside room)) pushedZeros
  have savedReg : ControlSaved args out.values := by
    intro j h
    apply ret.saved
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    omega
  have roll : sp-144+8 = sp-136 := by bv_omega
  have registers : LoopRegisters a out.values sp i c :=
    ⟨roll ▸ ret.rsp,
      (ret.saved 12 (by decide)).trans (arguments.width.trans st.registers.width),
      (ret.saved 15 (by decide)).trans (arguments.bitIndex.trans st.registers.bitIndex),
      (ret.saved 14 (by decide)).trans (arguments.length.trans st.registers.length),
      (ret.saved 5 (by decide)).trans (arguments.offsetNeg.trans st.registers.negIndex),
      (ret.saved 13 (by decide)).trans (arguments.carry.trans st.registers.carry),
      arguments.saved.trans savedReg⟩
  have offset : out.values[3].get 64 = BitVec.ofNat 64 (i%64) :=
    congrArg (Value.get 64) ((ret.saved 3 (by decide)).trans arguments.offset)
  have index0 : i/64 = 0 ↔ i < 64 := by omega
  obtain ⟨r,s,shiftBranch,shift,post,window⟩ := shiftWindow registers bound offset
    (by simpa only [index0] using ax) (by simpa only [index0] using dx)
  obtain ⟨t,branch,last,word,dst⟩ := classifyWindow post bound st.carry window fields
    (stackRead ctx frame (off := 96) (by decide) (by decide))
    (stackRead ctx frame (off := 120) (by decide) (by decide))
  refine ⟨t,q,?_,⟨last,frame,saved,fields,it',bytes,st.index,st.carry,by omega⟩,word,dst⟩
  intro result tail
  apply ParseSignature.exec_call call exe
  · rw [ret.tag, retAt]
    rfl
  · rw [resume]
    exact jump shiftBranch (jump shift (jump branch tail))

private theorem finishLoop {a b : Registers} {orig m : Ram} {sp dst next lo hi : BitVec 64}
    {c previous : Nat} {ds : List Int}
    (ctx : MemoryContext a orig sp dst)
    (st : LoopState a b orig m sp dst next lo hi 128 c previous ds) :
    let result := ds ++ (if c = 0 then [] else [1])
    ∃ out, program.Exec machine ⟨⟨.l11093a,b,m⟩,[]⟩ out ∧
      RoutineReturn a orig sp 0x110 [⟨dst.toNat,257⟩] out ∧
      out.values[0] = ⟨64,BitVec.ofNat 64 result.length⟩ ∧ DigitBytes out.store dst result := by
  obtain ⟨r,tail,rsp,len,kept⟩ := finalCarry st.registers st.carry st.fields
    (stackRead ctx st.frame (off := 136) (by decide) (by decide))
    (stackRead ctx st.frame (off := 120) (by decide) (by decide))
    (ctx.buffer.of_frame st.frame)
  have carry : c = 0 ∨ c = 1 := by have := st.carry; omega
  rcases carry with rfl | rfl
  · simp only [ite_true, List.append_nil] at tail ⊢
    have length : r[14].get 64 = BitVec.ofNat 64 ds.length := by rw [len, st.index]; rfl
    obtain ⟨out,run,rest⟩ := returnDigits ctx.entry st.frame ctx.separate st.saved kept
      (congrArg (Value.get 64) rsp) length st.bytes
    exact ⟨out,tail out run,rest⟩
  · simp only [Nat.one_ne_zero, ite_false] at tail ⊢
    let q := memStore m (digitAddr dst 128) (1 : BitVec 8)
    have frame := storeDigitFrame (ctx.buffer.of_frame st.frame) (i := 128) (by decide) (1 : BitVec 8)
    have hr := st.frame.trans frame writesDigits
    have saved := st.saved.of_frame frame (fun off l u =>
      slotOutsideDigits ctx.entry.room ctx.entry.returnSlot.low (by omega) l ctx.separate)
    have length : r[14].get 64 = BitVec.ofNat 64 (ds ++ [1]).length := by
      rw [len, List.length_append, st.index]
      rfl
    have bytes : DigitBytes q dst (ds ++ [1]) := by
      have h := digitBytes_append (d := 1) st.bytes (by rw [st.index]; decide)
      simpa only [st.index, show BitVec.ofInt 8 1 = 1 by decide, q] using h
    obtain ⟨out,run,rest⟩ := returnDigits ctx.entry hr ctx.separate saved kept
      (congrArg (Value.get 64) rsp) length bytes
    exact ⟨out,tail out run,rest⟩

set_option maxHeartbeats 1500000 in
theorem loopExec {a b : Registers} {orig m : Ram} {sp dst next lo hi : BitVec 64}
    {i c previous : Nat} {ds : List Int}
    (ctx : MemoryContext a orig sp dst)
    (st : LoopState a b orig m sp dst next lo hi i c previous ds)
    (limit : i ≤ 128) :
    let n := (hi ++ lo).toNat
    let result := ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c
    ∃ out, program.Exec machine ⟨⟨nextRound i,b,m⟩,[]⟩ out ∧
      RoutineReturn a orig sp 0x110 [⟨dst.toNat,257⟩] out ∧
      out.values[0] = ⟨64,BitVec.ofNat 64 result.length⟩ ∧ DigitBytes out.store dst result := by
  let n := (hi ++ lo).toNat
  let w := ((n/2^i) % (32 : Nat)) + c
  by_cases bound : i < 128
  · obtain ⟨r,m',read,st',word,dstReg⟩ := readAndClassify ctx st bound
    have canWrite := ctx.buffer.of_frame st'.frame
    have cap := stackRead ctx st'.frame (off := 136) (len := 8) (by decide) (by decide)
    have windowSmall : w ≤ 32 := by
      have small := Nat.mod_lt (n/2^i) (by decide : 0 < 32)
      have cy := st.carry
      dsimp only [w]
      omega
    have inBounds : i < 257 := by omega
    have keepFields : ∀ {q : Ram} (h : RamWriteFrame m' q [⟨dst.toNat,257⟩]),
        LoopMemory q sp dst := fun h => (preserveWrite ctx h st'.saved st'.fields st'.iterator).2.1
    by_cases even : w % 2 = 0
    · have read' : Continues .l110847 b m .l11089f r m' := by
        change Continues .l110847 b m (if w % 2 = 0 then .l11089f else .l1108d0) r m' at read
        rwa [ite_eq_left even] at read
      let mem := memStore m' (digitAddr dst i) (0 : BitVec 8)
      have wrote := storeDigitFrame canWrite inBounds (0 : BitVec 8)
      have frame := st'.frame.trans wrote writesDigits
      have ⟨saved,fields,iter⟩ := preserveWrite ctx wrote st'.saved st'.fields st'.iterator
      obtain ⟨s,step,regs⟩ := evenStep st'.registers st'.fields bound (congrArg (Value.get 64) dstReg) cap canWrite
        (stackRead ctx frame (off := 112) (by decide) (by decide)) fields.bits
      have bytes : DigitBytes mem dst (ds ++ [0]) := by
        have h := digitBytes_append (d := 0) st'.bytes (by rw [st'.index]; exact inBounds)
        simpa only [st'.index, show BitVec.ofInt 8 0 = 0 by decide, mem] using h
      have nextLen : (ds ++ [(0 : Int)]).length = i+1 := by simp only [List.length_append, st'.index, List.length_cons, List.length_nil]
      have cached := Naf.iterator_index_step (i := i) (j := i+1) (by omega) (by omega)
      have state : LoopState a s orig mem sp dst next lo hi (i+1) c (i/64) (ds ++ [0]) :=
        ⟨regs,frame,saved,fields,iter,bytes,nextLen,st'.carry,by omega⟩
      obtain ⟨out,execution,post,len,digits⟩ := loopExec ctx state (by omega)
      have eq : ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c =
          (ds ++ [0]) ++ Naf.recode (128-(i+1)+1) (128-(i+1)) (n/2^(i+1)) c := by
        rw [recodeEvenStep bound even, List.append_assoc]
      refine ⟨out, ?_, post, ?_, ?_⟩
      · rw [show nextRound i = .l110847 from ite_eq_left bound]
        exact read' out (step out execution)
      · change out.values[0] = ⟨64,BitVec.ofNat 64 (ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c).length⟩
        rwa [eq]
      · change DigitBytes out.store dst (ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c)
        rwa [eq]
    · have read' : Continues .l110847 b m .l1108d0 r m' := by
        change Continues .l110847 b m (if w % 2 = 0 then .l11089f else .l1108d0) r m' at read
        rwa [ite_eq_right even] at read
      have odd : w % 2 = 1 := by omega
      have input : n < 2^128 := (hi ++ lo).isLt
      have ⟨pos,fit,small,numeric⟩ := recodeOddStep (n := n) input bound st'.carry odd
      let s := Naf.skip (128-i) w
      have hb : i+s ≤ 128 := by change s ≤ 128-i at fit; omega
      let mem := memStore m' (digitAddr dst i) (BitVec.ofInt 8 (Naf.digit w))
      have wrote := storeDigitFrame canWrite inBounds (BitVec.ofInt 8 (Naf.digit w))
      have frame := st'.frame.trans wrote writesDigits
      let digit : Int := Naf.digit w
      have written : DigitBytes mem dst (ds ++ [digit]) := by
        have h := digitBytes_append (d := digit) st'.bytes (by rw [st'.index]; exact inBounds)
        simpa only [st'.index] using h
      have len : (ds ++ [digit]).length = i+1 := by
        simp only [List.length_append, st'.index, List.length_cons, List.length_nil]
      obtain ⟨u,step,regs⟩ := writeOddDigit st'.registers st'.fields bound windowSmall pos dstReg word cap
        (stackRead ctx st'.frame (off := 104) (by decide) (by decide))
        (stackRead ctx st'.frame (off := 124) (by decide) (by decide)) canWrite
        (stackRead ctx frame (off := 112) (by decide) (by decide)) (keepFields wrote).bits
      have padding : ∃ (v : Registers) (q : Ram), Continues (oddTail i w) u mem .l110833 v q ∧
          IndexAdvance a v sp i s (Naf.carry w) ∧ DigitBytes q dst ((ds ++ [digit]) ++ List.replicate (s-1) 0) ∧
          RamWriteFrame mem q [⟨dst.toNat,257⟩] := by
        by_cases one : s = 1
        · obtain ⟨v,via,regs'⟩ := advanceOne regs one
          have label : oddTail i w = .l110830 := ite_eq_left (by change s < 2; omega)
          rw [label]
          exact ⟨v,mem,via,by rw [one]; exact regs',digitBytes_append_zero written,.refl _ _⟩
        · have greater : 2 ≤ s := by change 1 ≤ s at pos; omega
          obtain ⟨v,q,via,regs',bytes,frm⟩ :=
            padOddDigit regs (canWrite.of_frame wrote) greater hb len written
          have label : oddTail i w = .l110912 := ite_eq_right (by change ¬s < 2; omega)
          exact ⟨v,q,by rwa [label],regs',bytes,frm⟩
      obtain ⟨v,q,pad,index,bytes,fr⟩ := padding
      have changed := wrote.trans fr (fun reg h => ⟨reg,h,Nat.le_refl _,Nat.le_refl _⟩)
      have ⟨saved,fields,iter⟩ := preserveWrite ctx changed st'.saved st'.fields st'.iterator
      have finished := st'.frame.trans changed writesDigits
      obtain ⟨tail,back,registers⟩ := advanceIndex index fields hb
        (stackRead ctx finished (off := 112) (by decide) (by decide))
      have prefixLen : ((ds ++ [digit]) ++ List.replicate (s-1) 0).length = i+s := by
        simp only [List.length_append, len, List.length_replicate]
        change 1 ≤ s at pos
        omega
      have cached := Naf.iterator_index_step (i := i) (j := i+s) (by omega) (by change s ≤ 5 at small; omega)
      have state : LoopState a tail orig q sp dst next lo hi (i+s) (Naf.carry w) (i/64)
          ((ds ++ [digit]) ++ List.replicate (s-1) 0) :=
        ⟨registers,finished,saved,fields,iter,bytes,prefixLen,Naf.carry_le_one w,by omega⟩
      obtain ⟨out,execution,post,length,output⟩ := loopExec ctx state hb
      have eq : ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c =
          ((ds ++ [digit]) ++ List.replicate (s-1) 0) ++
            Naf.recode (128-(i+s)+1) (128-(i+s)) (n/2^(i+s)) (Naf.carry w) := by
        rw [numeric]
        simp only [List.append_assoc]
        rfl
      refine ⟨out, ?_, post, ?_, ?_⟩
      · rw [show nextRound i = .l110847 from ite_eq_left bound]
        exact read' out (step out (pad out (back out execution)))
      · change out.values[0] = ⟨64,BitVec.ofNat 64 (ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c).length⟩
        rwa [eq]
      · change DigitBytes out.store dst (ds ++ Naf.recode (128-i+1) (128-i) (n/2^i) c)
        rwa [eq]
  · have eq : i = 128 := by omega
    subst i
    have result : Naf.recode (128-128+1) (128-128) (n/2^128) c =
        if c = 0 then [] else [1] := by simp [Naf.recode]
    dsimp only
    rw [result, show nextRound 128 = .l11093a from ite_eq_right (by decide)]
    exact finishLoop ctx st
termination_by 128-i
decreasing_by
  all_goals
    first
    | omega
    | change 1 ≤ s at pos
      simp only [n, w, s] at pos
      omega

set_option maxHeartbeats 1200000 in
theorem execute {a : Registers} {m : Ram} {sp dst src : BitVec 64}
    (ctx : MemoryContext a m sp dst) (di : a[7].get 64 = dst) (si : a[6].get 64 = 257)
    (dx : a[2].get 64 = src) (cx : a[1].get 64 = 16)
    (r8 : a[8].get 64 = 128) (r9 : a[9].get 64 = 5)
    (input : Readable m src 16) (zero : DigitBytes m dst [])
    (srcApart : Outside [scratch sp 0x110, ⟨dst.toNat,257⟩] src 16) :
    let digits := Naf.digits (memLoad m src 128).toNat
    ∃ out, program.Exec machine ⟨⟨.l1107b0,a,m⟩,[]⟩ out ∧
      RoutineReturn a m sp 0x110 [⟨dst.toNat,257⟩] out ∧
      out.values[0] = ⟨64,BitVec.ofNat 64 digits.length⟩ ∧ DigitBytes out.store dst digits := by
  let stagedMem := staged a m sp dst
  have room := ctx.entry.room
  have low := ctx.entry.returnSlot.low
  have stagedFrame : RamWriteFrame m stagedMem (writes sp dst) :=
    (RamWriteFrame.refl m _).trans (stageFrame (dst := dst) ctx.entry) writesScratch
  have zeroStage := digitBytes_of_frame (stageFrame (dst := dst) ctx.entry) (outsideScratch ctx.separate) zero
  obtain ⟨args,call,initArgs⟩ := callInitialize ctx.entry di si dx cx r8 r9
  have initKeep : ControlSaved a args := by
    intro ⟨j,hj⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact initArgs.df
    · exact initArgs.mxcsr
    · exact initArgs.ftw
    · exact initArgs.fcw
  have initEntry := iteratorEntry ctx.entry ctx.buffer stagedFrame initArgs.rsp initArgs.savedWidth
    initKeep (stagedReturn a m sp dst) (by decide)
  have apartInit : Outside [scratch (sp-144) 24] src 16 :=
    outsideWithin srcApart (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      have h := childInside room (scratch (sp-144) 24) List.mem_cons_self
      obtain ⟨reg, hm, hl, hu⟩ := h
      obtain rfl := List.mem_singleton.mp hm
      exact ⟨_,List.mem_cons_self,hl,hu⟩)
  have slot : Writable Extracted.programImage stagedMem (sp-88) 40 :=
    (stackSlot ctx.entry (by decide) (by decide : 40 ≤ (88 : BitVec 64).toNat)).of_frame stagedFrame
  obtain ⟨out,child,post,it⟩ := initializeIterator initEntry initArgs.dst initArgs.srcEq initArgs.length
    (input.of_frame stagedFrame) slot apartInit (bufferSeparate room low)
  have frame := stagedFrame.trans post.frame (childWrites room)
  have changeLo : memLoad stagedMem src 64 = memLoad m src 64 := by
    apply stagedFrame.memLoad_eq
    refine ⟨by have := srcApart.1; omega, fun r hr => ?_⟩
    rcases srcApart.2 r hr with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  have changeHi : memLoad stagedMem (src+8) 64 = memLoad m (src+8) 64 := by
    have s : (src+8).toNat = src.toNat+8 :=
      toNat_of_offsets (n := 8) rfl (addr_self _) input.low (by decide)
    apply stagedFrame.memLoad_eq
    refine ⟨by rw [s]; have := srcApart.1; omega, fun r hr => ?_⟩
    rw [s]
    rcases srcApart.2 r hr with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [changeLo, changeHi] at it
  let hi := memLoad m (src+8) 64
  let lo := memLoad m src 64
  have combine : hi ++ lo = memLoad m src 128 := by
    dsimp only [hi, lo]
    have hiWord : (memLoad m src 128).extractLsb' 64 64 = memLoad m (src+8) 64 :=
      extractLsb'_memLoad m src (n := 128) 64 64 (by decide) (by decide) (by decide)
    have loWord : (memLoad m src 128).extractLsb' 0 64 = memLoad m src 64 := by
      have h := extractLsb'_memLoad m src (n := 128) 0 64 (by decide) (by decide) (by decide)
      have addr : src + BitVec.ofNat 64 (0/8) = src := by bv_omega
      rwa [addr] at h
    rw [← hiWord, ← loWord]
    exact BitVec.extractLsb'_append_extractLsb'
  have childSpace : ∀ k : BitVec 64, 8 ≤ k.toNat → k.toNat ≤ 48 →
      Outside [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] (sp-k) 8 :=
    fun _ hl hu => skipChildWrites room low (by omega) hl (Or.inr hu)
  have saved := (stagedSaved a m sp dst).of_frame post.frame childSpace
  have dstWord : memLoad out.store (sp-120) 64 = dst :=
    (post.frame.memLoad_eq (skipChildWrites room low (by decide) (by decide) (Or.inl (by decide)))).trans
      (stagedDest a m sp dst)
  have outWrite := (stackSlot ctx.entry (off := 136) (by decide) (by decide : 48 ≤ (136 : BitVec 64).toNat)).of_frame frame
  have outStack : out.values[4] = ⟨64,sp-136⟩ := by
    have h : sp-144+8 = sp-136 := by bv_omega
    rw [post.rsp,h]
  have outCapacity : out.values[15].get 64 = 257 :=
    (congrArg (Value.get 64) (post.saved 15 (by decide))).trans initArgs.capacity
  have outBits : out.values[13].get 64 = 128 :=
    (congrArg (Value.get 64) (post.saved 13 (by decide))).trans initArgs.bits
  have outWidth : out.values[12] = ⟨64,5⟩ := (post.saved 12 (by decide)).trans initArgs.width
  have outRadix : out.values[3].get 64 = 32 :=
    (congrArg (Value.get 64) (post.saved 3 (by decide))).trans initArgs.windowMod
  obtain ⟨u,v,first,next,regs⟩ := enterLoop outStack outCapacity outBits outWidth outRadix outWrite
  let localRegion : MemoryRegion := ⟨sp.toNat-136, 48⟩
  have localFrame : RamWriteFrame out.store (writeLocals out.store sp) [localRegion] :=
    writeLocalsFrame (by omega) (by omega)
  have within : RegionsWithin [localRegion] [scratch sp 0x110] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [scratch,localRegion]
    omega
  have localSaved : SavedAt a sp (writeLocals out.store sp) := by
    apply saved.of_frame localFrame
    intro k hl hu
    refine ⟨by rw [subNat (by omega)]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    simp only [localRegion, subNat (by omega : k.toNat ≤ sp.toNat)]
    omega
  have localIterator : IteratorAt (writeLocals out.store sp) (sp-88) (src+16) 0 lo hi := by
    apply WordsAt.of_frame it localFrame (by decide)
    have s : (sp-88).toNat = sp.toNat-88 := subNatConst (sp := sp) (k := 88) (by omega)
    refine ⟨by rw [s]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    simp only [localRegion,s]
    omega
  have childKeep : ControlSaved args out.values := by
    intro j h
    apply post.saved
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    omega
  have live : LoopRegisters a v sp 0 0 :=
    ⟨regs.stack,regs.width,regs.bitIndex,regs.length,regs.negIndex,regs.carry,(initKeep.trans childKeep).trans regs.saved⟩
  have apart : Outside [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] dst 257 :=
    outsideWithin (outsideScratch ctx.separate) (childInside room)
  have values := digitBytes_of_frame localFrame (outsideWithin (outsideScratch ctx.separate) within)
    (digitBytes_of_frame post.frame apart zeroStage)
  have state : LoopState a v m (writeLocals out.store sp) sp dst (src+16) lo hi 0 0 0 [] :=
    ⟨live,frame.trans localFrame (fun r hr => by
      obtain ⟨big,hb,lb,ub⟩ := within r hr
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨_,List.mem_cons_self,lb,ub⟩),localSaved,writeLocalsMemory dstWord,localIterator,values,rfl,by decide,by decide⟩
  obtain ⟨final,run,rest,len,bytes⟩ := loopExec ctx state (by decide)
  refine ⟨final, ?_, rest, ?_, ?_⟩
  · apply ParseSignature.exec_call call child
    · rw [post.tag, stagedReturn]
      rfl
    · rw [resume]
      exact jump first (jump next run)
  · simpa only [Naf.digits, Nat.sub_zero, Nat.pow_zero, Nat.div_one, List.nil_append, combine] using len
  · simpa only [Naf.digits, Nat.sub_zero, Nat.pow_zero, Nat.div_one, List.nil_append, combine] using bytes

end K256.Proofs.Verify.Core.Lincomb.Recode
