import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport
import K256.Proofs.Generate.Generator.Multiply.Caller.TableCopies

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private abbrev tableCopyKept := [9, 13, 15, 22, 39, 50, 51]

private theorem reachesTableCopyJump {l l' : Label} {a b : Registers} {m : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l, a, m⟩ = .jump ⟨l', b, m⟩) :
    Reaches l a m l' b m := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ _ = _
  rw [step]
  rfl

private theorem windowTableCopySetup {a : Registers} {m : Ram} {sp src : BitVec 64}
    (rsp : a[4] = ⟨64, sp⟩)
    (stack : Readable m (sp - 0x220) 0xcb8)
    (active : memLoad m (sp + 0x1a0) 64 = 1)
    (source : memLoad m (sp + 0x1c0) 64 = src)
    (first : memLoad m (sp + 0x268) 64 = 66)
    (second : memLoad m (sp + 0x260) 64 = 66) :
    ∃ b, Reaches .l11f5e5 a m .l11f61c b m ∧
      b[4] = ⟨64, sp⟩ ∧ b[3] = ⟨64, src⟩ ∧ b[14] = ⟨64, 0⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ tableCopyKept → b[i] = a[i] := by
  have r4 : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  have readActive : LoadOk m (sp + 0x1a0) 8 := by slot_guard using code_l11f5e5
  have readSource : LoadOk m (sp + 0x1c0) 8 := by slot_guard using code_l11f5f4
  have readFirst : LoadOk m (sp + 0x268) 8 := by slot_guard using code_l11f600
  have readSecond : LoadOk m (sp + 0x260) 8 := by slot_guard using code_l11f60e
  let b1 : Registers := ?b1
  let b2 : Registers := ?b2
  let b3 : Registers := ?b3
  let b4 : Registers := ?b4
  have runActive : program.runBlock (dialect Extracted.programImage) ⟨.l11f5e5, a, m⟩ =
      .jump ⟨.l11f5f4, b1, m⟩ := by
    arithmetic_segment using code_l11f5e5 [r4, readActive, active]
  have runSetup : program.runBlock (dialect Extracted.programImage) ⟨.l11f5f4, b1, m⟩ =
      .jump ⟨.l11f600, b2, m⟩ := by
    arithmetic_segment using code_l11f5f4 [r4, readSource, source]
  have runFirst : program.runBlock (dialect Extracted.programImage) ⟨.l11f600, b2, m⟩ =
      .jump ⟨.l11f60e, b3, m⟩ := by
    arithmetic_segment using code_l11f600 [r4, readFirst, first]
  have runSecond : program.runBlock (dialect Extracted.programImage) ⟨.l11f60e, b3, m⟩ =
      .jump ⟨.l11f61c, b4, m⟩ := by
    arithmetic_segment using code_l11f60e [r4, readSecond, second]
  refine ⟨b4, (reachesTableCopyJump runActive).trans ((reachesTableCopyJump runSetup).trans
    ((reachesTableCopyJump runFirst).trans (reachesTableCopyJump runSecond))), rsp, rfl, rfl, ?_⟩
  rintro ⟨i, hi⟩ hm
  simp only [tableCopyKept, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


private theorem windowFirstTableCall {a : Registers} {m : Ram} {sp src : BitVec 64}
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = src)
    (slot : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l11f61c, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x11f638 : BitVec 64)⟩ (callFrame .l11f638 0x11f638) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 0x850 ∧ b[6].get 64 = src ∧
      b[2].get 64 = 960 ∧ b[3] = a[3] ∧ b[5] = ⟨64, 0x12a820⟩ ∧
      b[12] = ⟨64, sp + 0x850⟩ ∧ b[14] = a[14] ∧
      ∀ i : Fin Reg.count, i.val ∈ tableCopyKept → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x11f636 2 := by
    slot_guard using code_l11f61c
  refine ⟨?_, ?run, ?post⟩
  case run => arithmetic_segment using code_l11f61c [rsp, rbx, push]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ hm
    simp only [tableCopyKept, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem windowSecondTableCall {a : Registers} {m : Ram} {sp src : BitVec 64}
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = src) (rbp : a[5].get 64 = 0x12a820)
    (slot : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l11f638, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x11f64e : BitVec 64)⟩ (callFrame .l11f64e 0x11f64e) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 0x490 ∧ b[6].get 64 = src + 960 ∧
      b[2].get 64 = 960 ∧ ∀ i : Fin Reg.count, i.val ∈ Caller.memcpyPreserved → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x11f64c 2 := by
    slot_guard using code_l11f638
  refine ⟨?_, ?run, ?post⟩
  case run => arithmetic_segment using code_l11f638 [rsp, rbx, rbp, push]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ hm
    simp only [Caller.memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem windowMemcpyArgWidths {a : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820,a,m⟩,[]⟩ out)
    (r9 : a[9].width = 64) : ParseSignature.ArgumentWidths out.values := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .done out at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, Outcome.done.injEq, reduceCtorEq] at h
    all_goals
      subst out
      rintro ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact r9
  | next h _ =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, reduceCtorEq] at h


private theorem resumeWindowTableCopy {l next : Label} {a b : Registers} {m : Ram}
    {sp src dst ret : BitVec 64} {point : Standards.SECG.ECC.Curve.Point}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ =
      .call ⟨.l12a820,b,memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (rdi : b[7].get 64 = dst) (rsi : b[6].get 64 = src)
    (rdx : b[2].get 64 = 960) (df : b[22].get 1 = 0) (r9 : b[9].width = 64)
    (slot : Readable m (sp - 8) 8) (readSrc : Readable m src 960)
    (writeDst : Writable Extracted.programImage m dst 960)
    (slotBefore : (sp - 8).toNat + 8 ≤ dst.toNat) (dstBefore : dst.toNat + 960 ≤ src.toNat)
    (low : ret.toNat < 2^32) (table : TableAt m src point) :
    ∃ c n, Reaches l a m next c n ∧ c[4] = ⟨64,sp⟩ ∧ ParseSignature.ArgumentWidths c ∧
      (∀ i : Fin Reg.count, i.val ∈ Caller.memcpyPreserved → c[i] = b[i]) ∧
      RamWriteFrame m n [⟨(sp - 8).toNat,8⟩,⟨dst.toNat,960⟩] ∧ TableAt n dst point := by
  let pushed := memStore m (sp - 8) ret
  have slotLow := slot.low
  have srcLow := readSrc.low
  have dstLow := writeDst.readable.low
  have tag : memLoad pushed (sp - 8) 64 = ret :=
    memLoad_memStore_same m (sp - 8) ret (by decide) (by decide)
  have apart : RangeApart dst 960 (sp - 8) 8 :=
    RangeApart.of_toNat (by omega) (by omega) (Or.inr slotBefore)
  obtain ⟨out, run, store, gate, _, back, keep⟩ := Serialize.memcpy rdi rsi rdx rsp df
    (readSrc.memStore _ ret) (writeDst.memStore _ ret) (Or.inr dstBefore) apart
    (slot.memStore _ ret) (tag ▸ low)
  have path := Sample.reachesAfterSampleCall call run (tag ▸ gate) []
  have retInside {regions : List MemoryRegion} (member : ⟨(sp - 8).toNat,8⟩ ∈ regions) :
      InRegions regions (sp - 8) 8 := ⟨_, member, Nat.le_refl _, Nat.le_refl _, by omega⟩
  have afterPush : RamWriteFrame m pushed [⟨(sp - 8).toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore ret (retInside (.head _))
  refine ⟨out.values, out.store, path, ?_, windowMemcpyArgWidths run r9, keep, ?_, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using back
  · rw [store]
    apply Sec1.Wrapper.Copy.memCopy_frame (n := 960)
    · exact (RamWriteFrame.refl _ _).memStore ret (retInside (.head _))
    · exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _, by omega⟩
  · rw [store]
    apply TableAt.memCopy (table.of_frame afterPush ?_)
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    omega

set_option maxHeartbeats 600000 in
set_option maxRecDepth 512 in
theorem windowCopyTables {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat} {p : Projective}
    (entry : CoreEntry fr initial d) (s : RoundState fr d k .l11f5e5 a m)
    (acc : p.Stored m (fr.rsp - 0xb90)) :
    ∃ b n, Reaches .l11f5e5 a m .l11f64e b n ∧ RoundState fr d k .l11f64e b n ∧
      p.Stored n (fr.rsp - 0xb90) ∧ TableAt n (fr.rsp - 0xcb8 + 0x850) (firstBase d) ∧
      TableAt n (fr.rsp - 0xcb8 + 0x490) (secondBase d) ∧
      b[12].get 64 = fr.rsp - 0xcb8 + 0x850 ∧ b[14].get 64 = 0 := by
  let sp := fr.rsp - 0xcb8
  have atoms := s.atoms
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp,df,_,_,_,_,_,_,_,_,_,_,_,_,stack,_,_,_,_,_,_,_,_⟩ := atoms
  have below : sp - 0x220 = fr.rsp - 0xed8 := by dsimp only [sp]; bv_omega
  have readStack : Readable m (sp - 0x220) 0xcb8 := by
    rw [below]
    exact stack.readable.sub (Nat.le_refl _) (by omega)
  have slot : Writable Extracted.programImage m (sp - 8) 8 := by
    dsimp only [sp]
    slot_state region
  have leftDst : Writable Extracted.programImage m (sp + 0x850) 960 := by
    dsimp only [sp]
    slot_state region
  have rightDst : Writable Extracted.programImage m (sp + 0x490) 960 := by
    dsimp only [sp]
    slot_state region
  have tableStorage := entry.tableWrite.readable.of_frame s.memory.frame
  have readL : Readable m fr.rcx 960 :=
    tableStorage.sub (Nat.le_refl _) (by omega)
  have readR : Readable m (fr.rcx + 960) 960 :=
    tableStorage.of_offsets rfl (addr_self _) (by decide)
  have room := entry.room
  have high := entry.high
  have retNat : (sp - 8).toNat = fr.rsp.toNat - 0xcc0 := by
    dsimp only [sp]
    rw [show fr.rsp - 0xcb8 - 8 = fr.rsp - 0xcc0 by bv_omega, entry.stackOffset _ (by decide)]
    rfl
  have leftNat : (sp + 0x850).toNat = fr.rsp.toNat - 0x468 := by
    dsimp only [sp]
    rw [show fr.rsp - 0xcb8 + 0x850 = fr.rsp - 0x468 by bv_omega, entry.stackOffset _ (by decide)]
    rfl
  have rightNat : (sp + 0x490).toNat = fr.rsp.toNat - 0x828 := by
    dsimp only [sp]
    rw [show fr.rsp - 0xcb8 + 0x490 = fr.rsp - 0x828 by bv_omega, entry.stackOffset _ (by decide)]
    rfl
  have srcLNat : fr.rcx.toNat = fr.rsp.toNat + 4008 := by
    rw [entry.tablePtr, entry.aboveStack _ (by decide)]
    rfl
  have srcRNat : (fr.rcx + 960).toNat = fr.rsp.toNat + 4968 := by
    rw [entry.tablePtr, BitVec.add_assoc, show (0xfa8 : BitVec 64) + 960 = 4968 by decide,
      entry.aboveStack _ (by decide)]
    rfl
  obtain ⟨b, setup, bsp, bsrc, bzero, bkeep⟩ := windowTableCopySetup (sp := sp) (src := fr.rcx) rsp readStack
    (s.memory.locals (0x1a0,1) (by simp)) (s.memory.locals (0x1c0,fr.rcx) (by simp))
    (s.memory.locals (0x268,66) (by simp)) (s.memory.locals (0x260,66) (by simp))
  obtain ⟨c, firstCall, csp, cdst, csrc, clen, c3, c5, c12, c14, ckeep⟩ :=
    windowFirstTableCall (sp := sp) (src := fr.rcx) (congrArg (Value.get 64) bsp) (congrArg (Value.get 64) bsrc) slot
  have keptFirst (i : Fin Reg.count) (hi : i.val ∈ tableCopyKept) : c[i] = a[i] :=
    (ckeep i hi).trans (bkeep i hi)
  have cdf : c[22].get 1 = 0 := congrArg (Value.get 1) ((keptFirst 22 (by decide)).trans df)
  have c9 : c[9].width = 64 := (keptFirst 9 (by decide)) ▸ s.widths 9 (by decide)
  obtain ⟨e, m', firstRun, esp, _, ekeep, firstFrame, leftTable⟩ :=
    resumeWindowTableCopy (sp := sp) (src := fr.rcx) (dst := sp + 0x850) firstCall csp cdst csrc clen cdf c9 slot.readable readL leftDst
      (by rw [retNat,leftNat]; omega) (by rw [leftNat,srcLNat]; omega) (by decide)
      s.memory.firstTable
  have rightSource : TableAt m' (fr.rcx + 960) (secondBase d) := by
    apply s.memory.secondTable.of_frame firstFrame
    simp only [Outside, srcRNat, retNat, leftNat, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨by omega, ?_⟩
    rintro r (rfl | rfl) <;> dsimp only <;> omega
  obtain ⟨f, secondCall, fsp, fdst, fsrc, flen, fkeep⟩ :=
    windowSecondTableCall (sp := sp) (src := fr.rcx) (congrArg (Value.get 64) esp)
      (congrArg (Value.get 64) ((ekeep 3 (by decide)).trans (c3.trans bsrc)))
      (congrArg (Value.get 64) ((ekeep 5 (by decide)).trans c5)) (slot.of_frame firstFrame)
  have move (i : Fin Reg.count) (hi : i.val ∈ Caller.memcpyPreserved) : f[i] = c[i] :=
    (fkeep i hi).trans (ekeep i hi)
  have fdf : f[22].get 1 = 0 := (congrArg (Value.get 1) (move 22 (by decide))).trans cdf
  have f9 : f[9].width = 64 := (move 9 (by decide)) ▸ c9
  obtain ⟨g, n, secondRun, gsp, gw, gkeep, secondFrame, rightTable⟩ :=
    resumeWindowTableCopy (sp := sp) (src := fr.rcx + 960) (dst := sp + 0x490) secondCall fsp fdst fsrc flen fdf f9
      (slot.readable.of_frame firstFrame) (readR.of_frame firstFrame) (rightDst.of_frame firstFrame)
      (by rw [retNat,rightNat]; omega) (by rw [rightNat,srcRNat]; omega) (by decide)
      rightSource
  have keep (i : Fin Reg.count) (hi : i.val ∈ Caller.memcpyPreserved) : g[i] = c[i] :=
    (gkeep i hi).trans (move i hi)
  have saved : SavedWidths g := by
    rintro ⟨i, hi⟩ hm
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width ((keep 3 (by decide)).trans (c3.trans bsrc))
    · exact congrArg Value.width ((keep 5 (by decide)).trans c5)
    · exact congrArg Value.width ((keep 12 (by decide)).trans c12)
    · exact (congrArg Value.width ((keep 13 (by decide)).trans (keptFirst 13 (by decide)))).trans
        (s.saved 13 (by decide))
    · exact congrArg Value.width ((keep 14 (by decide)).trans (c14.trans bzero))
    · exact (congrArg Value.width ((keep 15 (by decide)).trans (keptFirst 15 (by decide)))).trans
        (s.saved 15 (by decide))
  have frame : RamWriteFrame m n (roundWrites sp) :=
    ((RamWriteFrame.refl _ _).trans firstFrame (by dsimp only [sp]; round_within using entry)).trans
      secondFrame (by dsimp only [sp]; round_within using entry)
  have state := s.afterWrites entry (t := .l11f64e) rfl rfl frame (by
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact gsp.trans rsp.symm
    · exact (keep 22 (by decide)).trans (keptFirst 22 (by decide))
    · exact (keep 39 (by decide)).trans (keptFirst 39 (by decide))
    · exact (keep 50 (by decide)).trans (keptFirst 50 (by decide))
    · exact (keep 51 (by decide)).trans (keptFirst 51 (by decide))) gw saved
  have leftAddress : g[12] = ⟨64, sp + 0x850⟩ := (keep 12 (by decide)).trans c12
  have zero : g[14] = ⟨64, 0⟩ := (keep 14 (by decide)).trans (c14.trans bzero)
  have leftGet : g[12].get 64 = sp + 0x850 := by
    change Value.get 64 g[12] = Value.get 64 ⟨64, sp + 0x850⟩
    exact congrArg (Value.get 64) leftAddress
  have zeroGet : g[14].get 64 = 0 := by
    change Value.get 64 g[14] = Value.get 64 ⟨64, 0⟩
    exact congrArg (Value.get 64) zero
  refine ⟨g, n, setup.trans (firstRun.trans secondRun), state, ?_, ?_, rightTable, leftGet, zeroGet⟩
  · have preserved {dst : BitVec 64} (hd : dst.toNat = fr.rsp.toNat - 0x468 ∨
        dst.toNat = fr.rsp.toNat - 0x828) : Outside [⟨(sp - 8).toNat,8⟩,⟨dst.toNat,960⟩]
        (fr.rsp - 0xb90) 120 := by
      rw [Outside, retNat, entry.stackOffset _ (by decide)]
      simp only [BitVec.reduceToNat, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨by omega, ?_⟩
      rintro r (rfl | rfl) <;> dsimp only <;> omega
    exact (acc.of_frame firstFrame (preserved (.inl leftNat))).of_frame secondFrame (preserved (.inr rightNat))
  · apply leftTable.of_frame secondFrame
    simp only [Outside, leftNat, retNat, rightNat, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨by omega, ?_⟩
    rintro r (rfl | rfl) <;> dsimp only <;> omega

end K256.Proofs.Generate.Generator.Multiply
