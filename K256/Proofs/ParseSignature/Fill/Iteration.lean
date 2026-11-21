import K256.Proofs.ParseSignature.Fill.Memory
import K256.Proofs.ParseSignature.CopyWord
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.ParseSignature.Fill

open K256.Proofs.Common Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.LIR

structure LoopRegisters (fr : Activation) (i : Nat) (a : Registers) : Prop where
  width : a[3] = ⟨64, 256⟩
  stack : a[4] = ⟨64, fr.rsp - 72⟩
  limit : a[5] = ⟨64, 32⟩
  inputEnd : a[12] = ⟨64, fr.rdi + BitVec.ofNat 64 (32 - 8 * i)⟩
  remaining : a[13] = ⟨64, BitVec.ofNat 64 (32 - 8 * i)⟩
  destination : a[14] = ⟨64, fr.rdx⟩
  written : a[15] = ⟨64, BitVec.ofNat 64 (8 * i)⟩
  df : a[22] = ⟨1, 0⟩
  mxcsr : a[39] = ⟨32, fr.mxcsr⟩
  ftw : a[50] = ⟨16, fr.ftw⟩
  fcw : a[51] = ⟨16, fr.fcw⟩
  r8Width : a[8].width = 64
  r9Width : a[9].width = 64

def loopLabel (i : Nat) : Label := if i < 4 then .l127e2e else .l127e50

def loopState (i : Nat) (a : Registers) (m : Ram) : CFG.State Value Ram Label signature Reg.count :=
  ⟨⟨loopLabel i, a, m⟩, []⟩

def filledLimbs (fr : Activation) (m : Ram) (n : Nat) : Prop :=
  ∀ i < n, memLoad m (wordAddr fr.rdx 64 i) 64 = scalarWord fr.original fr.rdi i

private theorem jumpStep {code : CodeMap} {start next : Location Value Ram Label signature}
    (h : program.runBlock (dialect code) start = .jump next) :
    (program.sem (dialect code)).Step ⟨start, []⟩ ⟨next, []⟩ := by
  change program.step (dialect code) ⟨start, []⟩ = .next ⟨next, []⟩
  simp only [Program.step, h, Transfer.next]

set_option maxHeartbeats 1200000 in
theorem fillIteration {code : CodeMap} {fr : Activation}
    (hcode : ∀ x ∈ fnCode, x ∈ code) (pre : MemoryPre code fr)
    {i : Nat} (hi : i < 4) {a : Registers} {m : Ram}
    (regs : LoopRegisters fr i a) (frame : RamWriteFrame fr.original m (fillWrites fr))
    (limbs : filledLimbs fr m i) :
    ∃ next m',
      (program.sem (dialect code)).Reaches (loopState i a m) (loopState (i + 1) next m') ∧
      LoopRegisters fr (i + 1) next ∧ ArgumentWidths next ∧
      RamWriteFrame m m' (loopWrites fr) ∧ filledLimbs fr m' (i + 1) := by
  let left := BitVec.ofNat 64 (32 - 8 * i)
  let offset := BitVec.ofNat 64 (8 * i)
  let inputEnd := fr.rdi + left
  have hleftNat : left.toNat = 32 - 8 * i := by
    change (32 - 8 * i) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have hleft : 8 ≤ left.toNat := by rw [hleftNat]; omega
  let scratch := fr.rsp - 56
  let callSp := fr.rsp - 80
  let src := inputEnd - 8
  let dst := wordAddr fr.rdx 64 i
  have sourceAddr : src = fr.rdi + BitVec.ofNat 64 (8 * (3 - i)) := by
    have hoff : 32 - 8 * i = 8 * (3 - i) + 8 := by omega
    change fr.rdi + BitVec.ofNat 64 (32 - 8 * i) - 8 = _
    rw [hoff, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ (8 : BitVec 64)
  have sourceNat : src.toNat = fr.rdi.toNat + 8 * (3 - i) := by
    rw [sourceAddr, wordOffsetNat pre.input.low (by omega)]
  have scratchNat : scratch.toNat = fr.rsp.toNat - 56 := pre.stackNat (by decide : 56 ≤ 208)
  have callSpNat : callSp.toNat = fr.rsp.toNat - 80 := pre.stackNat (by decide : 80 ≤ 208)
  have sourceOutside : Outside (fillWrites fr) src 8 := by
    apply outsideSubset pre.inputOutside <;> rw [sourceNat] <;> omega
  have zeroStore : StoreOk code m scratch 8 0x127e41 9 :=
    storeOk_of_codeRange (off := 19) (pre.stackWord (d := 56) (by decide) frame)
      (fun x hx => hcode x (code_l127e2e x hx)) (by decide)
  obtain ⟨preCopy, prepJump, sizeWord, negWord, prepKeeps⟩ :=
    prepareCopyBlock hleft regs.stack regs.remaining zeroStore
  let zeroed := memStore m scratch (0 : BitVec 64)
  have zeroFrame : RamWriteFrame m zeroed [loopStack fr] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self .., pre.stackInLoop (d := 56) (by decide)⟩
  have gotWord : memLoad zeroed 0x203dd0 64 = 0x12a820 := by
    have h : Outside [loopStack fr] 0x203dd0 8 := by
      refine ⟨by decide, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      have apart := pre.gotOutside.2 (stackWindow fr) (List.mem_cons_self ..)
      change 0x203dd8 ≤ callSp.toNat ∨ callSp.toNat + 80 ≤ 0x203dd0 at apart
      change 0x203dd8 ≤ callSp.toNat ∨ callSp.toNat + 32 ≤ 0x203dd0
      omega
    exact (zeroFrame.memLoad_eq h).trans ((frame.memLoad_eq pre.gotOutside).trans pre.gotValue)
  have gotRead := (pre.gotReadable.of_frame frame).of_frame zeroFrame
  have retStore : StoreOk code zeroed callSp 8 0x127e0b 6 :=
    storeOk_of_codeRange (off := 27) ((pre.stackWord (d := 80) (by decide) frame).of_frame zeroFrame)
      (fun x hx => hcode x (code_l127df0 x hx)) (by decide)
  obtain ⟨ca, cont, copyTransfer, contLabel, contGuard, caCount, caSize, caSp, caSrc, caDst, callKeeps⟩ :=
    copyCallBlock ((prepKeeps 4 (by decide) (by decide)).trans regs.stack) sizeWord negWord
      ((prepKeeps 12 (by decide) (by decide)).trans regs.inputEnd)
      ((prepKeeps 13 (by decide) (by decide)).trans regs.remaining)
      retStore ⟨gotRead.low, gotRead.present⟩ gotWord
  let callMem := memStore zeroed callSp (0x127e11 : BitVec 64)
  have callFrame : RamWriteFrame m callMem [loopStack fr] :=
    zeroFrame.memStore _ ⟨_, List.mem_cons_self .., pre.stackInLoop (d := 80) (by decide)⟩
  let copyBase : Activation := { fr with
    original := callMem
    rsp := callSp
    ret := 0x127e11
    low := callSp
    rbx := 256
    rbp := 32
    r12 := inputEnd
    r13 := left
    r14 := fr.rdx
    r15 := offset }
  let cf := withArguments copyBase ca
  have caKept (r : Nat) (hr : r ∈ [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51])
      (bound : r < Reg.count) : ca[r] = a[r] := by
    have hp : r ∈ [3, 4, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    exact (callKeeps r hr bound).trans (prepKeeps r hp bound)
  have caWidths : ArgumentWidths ca := by
    intro ⟨r, bound⟩ hr
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width caDst
    · exact congrArg Value.width caSrc
    · exact congrArg Value.width caSize
    · exact congrArg Value.width caCount
    · exact (congrArg Value.width (caKept 8 (by decide) bound)).trans regs.r8Width
    · exact (congrArg Value.width (caKept 9 (by decide) bound)).trans regs.r9Width
  have cfSrc : cf.rsi = src := get64 caSrc
  have cfDst : cf.rdi = scratch := get64 caDst
  have cfSize : cf.rdx = 8 := get64 caSize
  have cfRead : Readable callMem cf.rsi 8 := by
    rw [cfSrc]
    apply ((pre.input.of_frame frame).of_frame callFrame).sub <;> rw [sourceNat] <;> omega
  have cfWrite : Writable code callMem cf.rdi 8 := by
    rw [cfDst]
    exact (pre.stackWord (d := 56) (by decide) frame).of_frame callFrame
  have cfRetRead : Readable callMem cf.rsp 8 :=
    (pre.stackWord (d := 80) (by decide) frame).readable.of_frame callFrame
  have cfSrcOutside : Outside [buffer cf.rdi 8] cf.rsi 8 := by
    rw [cfSrc, cfDst]
    refine ⟨sourceOutside.1, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    have sep := sourceOutside.2 (stackWindow fr) (List.mem_cons_self ..)
    have hs := pre.stackInWindow (d := 56) (by decide)
    change (stackWindow fr).start ≤ scratch.toNat ∧ scratch.toNat + 8 ≤
      (stackWindow fr).start + (stackWindow fr).size ∧ _ at hs
    change src.toNat + 8 ≤ scratch.toNat ∨ scratch.toNat + 8 ≤ src.toNat
    omega
  have cfRetOutside : Outside [buffer cf.rdi 8] cf.rsp 8 := by
    rw [cfDst]
    refine ⟨by have h := cfRetRead.low; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    change callSp.toNat + 8 ≤ scratch.toNat ∨ scratch.toNat + 8 ≤ callSp.toNat
    rw [callSpNat, scratchNat]
    have room := pre.stackRoom
    omega
  have cfAlign : cf.rdi.toNat % 8 = 0 := by
    rw [cfDst, scratchNat]
    have room := pre.stackRoom
    have align := pre.stackAlign
    omega
  have cfEntry : Atom.All code ca callMem (Fn12a820.frameInfo.entryAtoms cf) := by
    have arg (r : Fin Reg.count) (hr : r.val ∈ Activation.argumentNumbers) :
        ca[r] = cf.entryValue r := entryArgument caWidths copyBase r hr
    change Atom.All code ca callMem (Fn12a820.frameAt .l12a820 cf)
    simp only [Fn12a820.frameAt, Fn12a820.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨caSp, (caKept 22 (by decide) (by decide)).trans regs.df,
      arg 1 (by decide), arg 2 (by decide), (caKept 3 (by decide) (by decide)).trans regs.width,
      (caKept 5 (by decide) (by decide)).trans regs.limit, arg 6 (by decide), arg 7 (by decide),
      arg 8 (by decide), arg 9 (by decide), (caKept 12 (by decide) (by decide)).trans regs.inputEnd,
      (caKept 13 (by decide) (by decide)).trans regs.remaining,
      (caKept 14 (by decide) (by decide)).trans regs.destination,
      (caKept 15 (by decide) (by decide)).trans regs.written,
      (caKept 39 (by decide) (by decide)).trans regs.mxcsr, (caKept 50 (by decide) (by decide)).trans regs.ftw,
      (caKept 51 (by decide) (by decide)).trans regs.fcw, cfRetRead,
      memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, Nat.le_refl _, ?_, trivial⟩
    · change (0x127e11 : BitVec 64).toNat < 2^32
      decide
    · change callSp.toNat % 16 = 8
      rw [callSpNat]
      have room := pre.stackRoom
      have align := pre.stackAlign
      omega
  obtain ⟨copied, copyExec, copyTag, copyDone, copyFrame, copyWidths, copyValue⟩ :=
    memcpy_word_call hcode cf cfSize cfAlign cfRead cfWrite cfSrcOutside cfRetOutside _ cfEntry
  have copyWithin : RegionsWithin (cf.region :: [buffer cf.rdi 8]) [loopStack fr] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨loopStack fr, List.mem_cons_self .., ?_⟩
    rcases hr with rfl | rfl
    · change callSp.toNat ≤ callSp.toNat ∧ callSp.toNat + (callSp.toNat - callSp.toNat) ≤ callSp.toNat + 32
      omega
    · rw [cfDst]
      exact ⟨(pre.stackInLoop (d := 56) (by decide)).1, (pre.stackInLoop (d := 56) (by decide)).2.1⟩
  have copyStackFrame := callFrame.trans copyFrame copyWithin
  have copySource : memLoad callMem src 64 = memLoad fr.original src 64 := by
    have hout : Outside [loopStack fr] src 8 := by
      refine ⟨sourceOutside.1, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      have apart := sourceOutside.2 (stackWindow fr) (List.mem_cons_self ..)
      change src.toNat + 8 ≤ callSp.toNat ∨ callSp.toNat + 80 ≤ src.toNat at apart
      change src.toNat + 8 ≤ callSp.toNat ∨ callSp.toNat + 32 ≤ src.toNat
      omega
    exact (callFrame.memLoad_eq hout).trans (frame.memLoad_eq sourceOutside)
  have hword : memLoad copied.store scratch 64 = memLoad fr.original src 64 := by
    rw [← cfSrc] at copySource
    rw [← cfSrc, ← cfDst]
    exact copyValue.trans copySource
  change Atom.All code copied.values copied.store (Fn12a820.doneAt cf) at copyDone
  simp only [Fn12a820.doneAt, Atom.All, Atom.Holds] at copyDone
  obtain ⟨copySp, df, width, limit, endPtr, size, dest, written, mxcsr, ftw, fcw, _⟩ := copyDone
  have copySp' : copied.values[4] = ⟨64, fr.rsp - 72⟩ := by
    change copied.values[4] = ⟨64, fr.rsp - 80 + 8⟩ at copySp
    rwa [show fr.rsp - 80 + 8 = fr.rsp - 72 by bv_omega] at copySp
  have tmpReadable := (pre.stackWord (d := 56) (by decide) frame).readable.of_frame copyStackFrame
  obtain ⟨swapped, swapJump, swapValue, swapKeeps⟩ :=
    swapBlock copySp' ⟨tmpReadable.low, tmpReadable.present⟩
  rw [hword, sourceAddr] at swapValue
  change swapped[0] = ⟨64, scalarWord fr.original fr.rdi i⟩ at swapValue
  have dstBounds := pre.outputIn hi
  have dstWritable : Writable code copied.store dst 8 :=
    ((pre.output.of_frame frame).of_frame copyStackFrame).sub dstBounds.1 dstBounds.2.1
  have dstStore : StoreOk code copied.store dst 8 0x127e19 4 :=
    storeOk_of_codeRange (off := 0) dstWritable
      (fun x hx => hcode x (code_l127e19 x hx)) (by decide)
  obtain ⟨next, storeJump, newSrc, newCount, newOffset, storeKeeps⟩ :=
    storeLimbBlock swapValue ((swapKeeps 5 (by decide) (by decide)).trans limit)
      ((swapKeeps 12 (by decide) (by decide)).trans endPtr)
      ((swapKeeps 13 (by decide) (by decide)).trans size)
      ((swapKeeps 14 (by decide) (by decide)).trans dest)
      ((swapKeeps 15 (by decide) (by decide)).trans written) dstStore
  let m' := memStore copied.store dst (scalarWord fr.original fr.rdi i)
  have exitLabel : (if offset + 8 = 32 then Label.l127e50 else .l127e2e) = loopLabel (i + 1) := by
    have hoff : (offset + 8).toNat = 8 * (i + 1) := by
      change (BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8).toNat = _
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hexit : offset + 8 = 32 ↔ i = 3 := by
      constructor
      · intro hx
        rw [hx] at hoff
        change 32 = 8 * (i + 1) at hoff
        omega
      · intro hx
        subst i
        rfl
    unfold loopLabel
    by_cases h : i = 3
    · rw [ite_eq_left (hexit.mpr h), ite_eq_right (by omega)]
    · rw [ite_eq_right (fun e => h (hexit.mp e)), ite_eq_left (by omega)]
  have resumes : cont.resume copied = (⟨.l127e11, copied.values, copied.store⟩ : Location Value Ram Label signature) := by
    change (⟨cont.target, (cont.resume copied).arguments, copied.store⟩ : Location Value Ram Label signature) = _
    rw [contLabel, resume_arguments]
  have accepts : cont.Accepts (dialect code) copied.tag = true := by
    simp only [StackFrame.Accepts, contGuard, copyTag]
    rfl
  have callStep : (program.sem (dialect code)).Step ⟨⟨.l127df0, preCopy, zeroed⟩, []⟩
      ⟨⟨.l12a820, ca, callMem⟩, [cont]⟩ := by
    change program.step (dialect code) _ = _
    simp only [Program.step, copyTransfer, Transfer.next]
    rfl
  have acrossCall := exec_reaches_resume copyExec cont [] accepts
  rw [resumes] at acrossCall
  have across : (program.sem (dialect code)).Reaches (loopState i a m) (loopState (i + 1) next m') := by
    have labelNow : loopLabel i = .l127e2e := ite_eq_left hi
    have preStep := jumpStep prepJump
    have postStep := jumpStep swapJump
    change program.runBlock (dialect code) ⟨.l127e19, swapped, copied.store⟩ =
      .jump ⟨if offset + 8 = 32 then .l127e50 else .l127e2e, next, m'⟩ at storeJump
    rw [exitLabel] at storeJump
    have lastStep := jumpStep storeJump
    change (program.sem (dialect code)).Reaches ⟨⟨loopLabel i, a, m⟩, []⟩ _
    rw [labelNow]
    exact .step preStep (.step callStep ((acrossCall.tail postStep).tail lastStep))
  have finalWidths : ArgumentWidths next :=
    storeKeeps.widths (by
      intro r hr
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega) (swapKeeps.widths (by
      intro r hr
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega) copyWidths)
  have remainingSub : left - 8 = BitVec.ofNat 64 (32 - 8 * (i + 1)) := by
    change BitVec.ofNat 64 (32 - 8 * i) - BitVec.ofNat 64 8 = _
    rw [show 32 - 8 * i = (32 - 8 * (i + 1)) + 8 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ (8 : BitVec 64)
  have inputEndSub : inputEnd - 8 = fr.rdi + BitVec.ofNat 64 (32 - 8 * (i + 1)) := by
    change fr.rdi + left - 8 = _
    rw [show fr.rdi + left - 8 = fr.rdi + (left - 8) by bv_omega, remainingSub]
  have offsetAdd : offset + 8 = BitVec.ofNat 64 (8 * (i + 1)) := by
    change BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add, show 8 * i + 8 = 8 * (i + 1) by omega]
  have transfer (r : Nat) (hr : r ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 22, 39, 50, 51])
      (bound : r < Reg.count) : next[r] = copied.values[r] := by
    have hs : r ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    exact (storeKeeps r hr bound).trans (swapKeeps r hs bound)
  refine ⟨next, m', across, ?_, finalWidths, ?_, ?_⟩
  · exact ⟨(transfer 3 (by decide) (by decide)).trans width, (transfer 4 (by decide) (by decide)).trans copySp',
      (transfer 5 (by decide) (by decide)).trans limit,
      newSrc.trans (congrArg (fun w : BitVec 64 => (⟨64, w⟩ : Value)) inputEndSub),
      newCount.trans (congrArg (fun w : BitVec 64 => (⟨64, w⟩ : Value)) remainingSub),
      (transfer 14 (by decide) (by decide)).trans dest,
      newOffset.trans (congrArg (fun w : BitVec 64 => (⟨64, w⟩ : Value)) offsetAdd),
      (transfer 22 (by decide) (by decide)).trans df, (transfer 39 (by decide) (by decide)).trans mxcsr,
      (transfer 50 (by decide) (by decide)).trans ftw, (transfer 51 (by decide) (by decide)).trans fcw,
      finalWidths 8 (by decide), finalWidths 9 (by decide)⟩
  · have hf := (RamWriteFrame.refl m (loopWrites fr)).trans copyStackFrame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩)
    exact hf.memStore _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), dstBounds⟩
  · intro j hj
    by_cases he : j = i
    · subst j
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · have hj' : j < i := by omega
      have ht : j < 4 := by omega
      have out := pre.outputOutsideLoopStack ht
      have apart : RangeApart dst 8 (wordAddr fr.rdx 64 j) 8 := by
        apply RangeApart.of_toNat dstBounds.2.2 out.1
        right
        change (fr.rdx + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ (fr.rdx + BitVec.ofNat 64 (8 * i)).toNat
        rw [wordOffsetNat pre.output.readable.low (by omega), wordOffsetNat pre.output.readable.low (by omega)]
        omega
      change memLoad (memStore copied.store dst (scalarWord fr.original fr.rdi i))
        (wordAddr fr.rdx 64 j) 64 = _
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart, copyStackFrame.memLoad_eq out]
      exact limbs j hj'

end K256.Proofs.ParseSignature.Fill
