import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Tables
import K256.Proofs.Ecdh.Multiply.Loop.Body.Transport

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

open_generator_loop Body.Tables (tableCopyKept windowTableCopySetup windowFirstTableCall windowSecondTableCall resumeWindowTableCopy)

set_option maxHeartbeats 600000 in
theorem peerWindowCopyTables {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat} {peer : Projective} {p : Projective}
    (entry : PeerCoreEntry fr initial d peer) (s : PeerRoundState fr d peer k .l11f5e5 a m)
    (acc : p.Stored m (fr.rsp - 0xb90)) :
    ∃ b n, Reaches .l11f5e5 a m .l11f64e b n ∧ PeerRoundState fr d peer k .l11f64e b n ∧
      p.Stored n (fr.rsp - 0xb90) ∧ TableAt n (fr.rsp - 0xcb8 + 0x850) (peerFirstBase d peer) ∧
      TableAt n (fr.rsp - 0xcb8 + 0x490) (peerSecondBase d peer) ∧
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
  have srcLNat : fr.rcx.toNat = fr.rsp.toNat + 4192 := by
    rw [entry.tablePtr, entry.aboveStack _ (by decide)]
    rfl
  have srcRNat : (fr.rcx + 960).toNat = fr.rsp.toNat + 5152 := by
    rw [entry.tablePtr, BitVec.add_assoc, show (0x1060 : BitVec 64) + 960 = 5152 by decide,
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
  have rightSource : TableAt m' (fr.rcx + 960) (peerSecondBase d peer) := by
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
    ((RamWriteFrame.refl _ _).trans firstFrame (by dsimp only [sp]; peer_round_within using entry)).trans
      secondFrame (by dsimp only [sp]; peer_round_within using entry)
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
