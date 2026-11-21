import Sha3.Proofs.Update.Tail.Code
import Sha3.Proofs.Update.Tail.Context
import Sha3.Proofs.Update.Tail.Setup

namespace Sha3.Proofs.Update.Tail

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem frame_trans {pointer : BitVec 64} {s u t : RamState}
    (h : AgreesExcept (clobbers pointer) s u)
    (h' : AgreesExcept (clobbers pointer) u t) : AgreesExcept (clobbers pointer) s t :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

section Composition

variable [Bindings] {v : Variant} {pointer source completed : BitVec 64}
  {remaining : Nat} {initial input : Nat → UInt8} {s : RamState}
  (hc : Context v pointer source completed remaining initial input s)
  (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)

include hc hb in
theorem finish_result {u : RamState} (hr : ReadyToStep u)
    (hcode : CodeIn Extracted.programImage u) (hip : u.RIP = Setup.finishPC v)
    (hframe : AgreesExcept (clobbers pointer) s u)
    (hcursor : (Operand.reg 7 : Operand 64).read u = pointer + 200)
    (hbytes : Bytes u.external pointer 200
      (fun i ↦ initial i ^^^ (if i < remaining then input i else 0))) :
    ∃ t, Advances boundary 2 u t ∧ Result v pointer remaining initial input s t := by
  have hlt : remaining < 200 := Nat.lt_of_lt_of_le hc.remaining_lt v.rate_le
  have hremaining : (Operand.reg 12 : Operand 64).read u = BitVec.ofNat 64 remaining :=
    (hframe.read (by simp [clobbers])).trans hc.remainingReg
  obtain ⟨t, ha, htready, htcode, _, htip, htreg, htframe⟩ :=
    Setup.finish v ⟨remaining, hlt⟩ u hr hcode hb hip hremaining
  refine ⟨t, ha, htready, htcode, htip, htreg, (htframe.read (by decide)).trans hcursor, ?_, ?_⟩
  · simpa only [htframe.external (by simp [Component.Covers])] using hbytes
  · exact (hframe.trans htframe).mono (by simp [clobbers])

include hc hb in
theorem byte_result {u : RamState} (offset : Nat) (hpart : offset + remaining % 4 = remaining)
    (hpos : 0 < remaining % 4) (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hip : u.RIP = Setup.tailSetupPC v) (hframe : AgreesExcept (clobbers pointer) s u)
    (hcursor : (Operand.reg 7 : Operand 64).read u = pointer + 200)
    (h0 : (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 (remaining % 4))
    (h2 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 offset)
    (hcompleted : (Operand.reg 13 : Operand 64).read u = completed)
    (hsource : (Operand.reg 3 : Operand 64).read u = source)
    (hptr : (Operand.reg 15 : Operand 64).read u = pointer)
    (hbytes : Bytes u.external pointer 200
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0))) :
    ∃ fuel t, Advances boundary fuel u t ∧ Result v pointer remaining initial input s t := by
  obtain ⟨w, ha, hwready, hwcode, _, hwip, hwframe, hw0, hwindex, hwpointer, hwsource, hwcursor⟩ :=
    Setup.tail_setup v u hr hcode hb hip
  have hframew : AgreesExcept (clobbers pointer) s w :=
    frame_trans hframe (hwframe.mono (by simp [Setup.clobbers, clobbers]))
  have hwb : Bytes w.external pointer 200
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0)) := by
    simpa only [hwframe.external Setup.clobbers_nomem] using hbytes
  have hinput := hc.sourceBytes_of_frame hframew
  have hlt : remaining < 200 := Nat.lt_of_lt_of_le hc.remaining_lt v.rate_le
  have hspan : offset + remaining % 4 ≤ 200 := by omega
  have hsrcLow : (source + completed + BitVec.ofNat 64 offset).toNat + remaining % 4 ≤ 2 ^ 32 := by
    have hl := hc.sourceLow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hl ⊢
    omega
  have hinv : TailInvariant (byteAddress v) (source + completed + BitVec.ofNat 64 offset)
      pointer offset (remaining % 4) 200 initial input 0 w := by
    refine ⟨?_, hw0.trans h0, hwindex, ?_, ?_, hinput.sub offset _ (by omega), ?_⟩
    · simpa only [hpos, ↓reduceIte] using hwip
    · rw [hsource, hcompleted, h2] at hwsource
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using hwsource
    · rw [hptr, h2] at hwpointer
      simpa only [BitVec.ofNat_eq_ofNat] using hwpointer
    · simpa only [Nat.add_zero] using hwb
  obtain ⟨x, hloop, hxready, hxcode, hx, hxframe⟩ :=
    tail_loop boundary Extracted.programImage (byteAddress v)
      (source + completed + BitVec.ofNat 64 offset) pointer offset (remaining % 4) 200
      initial input hspan hsrcLow hc.stateLow
      (by
        intro i hi j hj he
        apply hc.apart i hi (offset + j) (by omega)
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he)
      (fun i hi hp ↦ hc.avoids i hi (Or.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (Or.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (tail_subset v)
      (by
        intro i hi
        apply byte_ne_boundary v boundary hb i
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega) w hwready hwcode hinv
  have hframex : AgreesExcept (clobbers pointer) s x :=
    frame_trans hframew (hxframe.mono (by simp [tailClobbers, clobbers]))
  have hxip : x.RIP = Setup.finishPC v := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, byteAddress, Setup.finishPC, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd] using hx.rip
  obtain ⟨t, hfinish, ht⟩ := finish_result hc boundary hb hxready hxcode hxip hframex
    ((hxframe.read (by simp [tailClobbers])).trans (hwcursor.trans hcursor))
    (by simpa only [hpart] using hx.stateBytes)
  exact ⟨_, t, (ha.trans hloop).trans hfinish, ht⟩

include hc hb in
theorem chunk_result {u : RamState} (hlarge : 4 ≤ remaining)
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hframe : AgreesExcept (clobbers pointer) s u)
    (hcursor : (Operand.reg 7 : Operand 64).read u = pointer + 200)
    (h0 : (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 (remaining % 4))
    (hcompleted : (Operand.reg 13 : Operand 64).read u = completed)
    (hsource : (Operand.reg 3 : Operand 64).read u = source)
    (hinv : ChunkInvariant (chunkAddress v) (source + completed) pointer
      (remaining / 4 * 4) 200 initial input 0 0 u) :
    ∃ fuel t, Advances boundary fuel u t ∧ Result v pointer remaining initial input s t := by
  have hlt : remaining < 200 := Nat.lt_of_lt_of_le hc.remaining_lt v.rate_le
  obtain ⟨w, ha, hwready, hwcode, hw, hwframe⟩ :=
    chunk_loop boundary Extracted.programImage (chunkAddress v) (source + completed) pointer
      (remaining / 4 * 4) 200 initial input (by omega) (by have := hc.sourceLow; omega)
      hc.stateLow (fun i hi j hj ↦ hc.apart i hi j (by omega))
      (fun i hi hp ↦ hc.avoids i hi (Or.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (Or.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (chunk_subset v) (chunk_ne_boundary v boundary hb)
      (remaining / 4) (by omega) u hr hcode hinv
  have hframew : AgreesExcept (clobbers pointer) s w :=
    frame_trans hframe (hwframe.mono (by simp [chunkClobbers, clobbers]))
  have hwip : w.RIP = Setup.postChunkPC v := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, Setup.postChunkPC, BitVec.ofNat_eq_ofNat] using hw.rip
  have hw0 : (Operand.reg 0 : Operand 64).read w = BitVec.ofNat 64 (remaining % 4) :=
    (hwframe.read (by simp [chunkClobbers])).trans h0
  obtain ⟨x, hxrun, hxready, hxcode, _, hxip, hxobs, hxframe⟩ :=
    Setup.postchunk_test v w hwready hwcode hb hwip
  have hframex : AgreesExcept (clobbers pointer) s x :=
    frame_trans hframew (hxframe.mono (by simp [Setup.clobbers, clobbers]))
  have hxbytes : Bytes x.external pointer 200
      (fun i ↦ initial i ^^^ (if i < remaining / 4 * 4 then input i else 0)) := by
    simpa only [hxframe.external Setup.clobbers_nomem, Nat.add_zero] using hw.stateBytes
  rw [hw0] at hxip
  simp only [BitVec.ofNat_eq_ofNat] at hxip
  by_cases hzero : remaining % 4 = 0
  · have hfull : remaining / 4 * 4 = remaining := by omega
    have hxip' : x.RIP = Setup.finishPC v := by
      simpa only [hzero, BitVec.ofNat_eq_ofNat, beq_self_eq_true, ↓reduceIte] using hxip
    obtain ⟨t, hfinish, ht⟩ := finish_result hc boundary hb hxready hxcode hxip' hframex
      ((hxobs.read_reg _).symm.trans ((hwframe.read (by simp [chunkClobbers])).trans hcursor))
      (by simpa only [hfull] using hxbytes)
    exact ⟨_, t, (ha.trans hxrun).trans hfinish, ht⟩
  · have hz : (BitVec.ofNat 64 (remaining % 4) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      have he' := congrArg BitVec.toNat (eq_of_beq he)
      simp only [BitVec.toNat_ofNat] at he'
      omega
    have hxip' : x.RIP = Setup.tailSetupPC v := by
      simpa only [hz, Bool.false_eq_true, ↓reduceIte] using hxip
    obtain ⟨fuel, t, htail, ht⟩ := byte_result hc boundary hb (remaining / 4 * 4)
      (by omega) (by omega) hxready hxcode hxip' hframex
      ((hxobs.read_reg _).symm.trans ((hwframe.read (by simp [chunkClobbers])).trans hcursor))
      ((hxobs.read_reg _).symm.trans hw0)
      ((hxobs.read_reg _).symm.trans hw.indexReg)
      ((hxobs.read_reg _).symm.trans ((hwframe.read (by simp [chunkClobbers])).trans hcompleted))
      ((hxobs.read_reg _).symm.trans ((hwframe.read (by simp [chunkClobbers])).trans hsource))
      ((hxobs.read_reg _).symm.trans hw.destinationReg) hxbytes
    exact ⟨_, t, (ha.trans hxrun).trans htail, ht⟩

include hc hb in
theorem advance : ∃ fuel t, Advances boundary fuel s t ∧
    Result v pointer remaining initial input s t := by
  obtain ⟨fuel, u, ha, huready, hucode, huframe, _, _, husource, hucompleted, huptr, hucursor, hcases⟩ :=
    Setup.dispatch v ⟨remaining, hc.remaining_lt⟩ s hc.ready hc.code hb hc.rip hc.remainingReg hc.cursorRead
  have hf : AgreesExcept (clobbers pointer) s u :=
    huframe.mono (by simp [Setup.clobbers, clobbers])
  have huinitial : Bytes u.external pointer 200 initial := by
    simpa only [huframe.external Setup.clobbers_nomem] using hc.stateBytes
  dsimp only at hcases
  rcases hcases with ⟨hzero, huip, hu2⟩ | ⟨hpos, hsmall, huip, hu0, hu2⟩ |
    ⟨hlarge, huip, hu0, hu1, hu2, hu6⟩
  · refine ⟨fuel, u, ha, huready, hucode, huip, ?_, hucursor.trans hc.cursorSlot, ?_, hf⟩
    · simpa only [hzero, BitVec.ofNat_eq_ofNat] using hu2
    · simpa only [hzero, Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial
  · have hmod : remaining % 4 = remaining := Nat.mod_eq_of_lt hsmall
    obtain ⟨fuel', t, htail, ht⟩ := byte_result hc boundary hb 0 (by omega) (by omega)
      huready hucode huip hf (hucursor.trans hc.cursorSlot) hu0 hu2 (hucompleted.trans hc.completedReg) (husource.trans hc.sourceReg)
      (huptr.trans hc.pointerReg)
      (by simpa only [Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial)
    exact ⟨_, t, ha.trans htail, ht⟩
  · have hinput : Bytes u.external (source + completed) remaining input :=
      hc.sourceBytes_of_frame hf
    have hinv : ChunkInvariant (chunkAddress v) (source + completed) pointer
        (remaining / 4 * 4) 200 initial input 0 0 u := by
      refine ⟨?_, hu1, hu2, ?_, ?_, ?_, ?_⟩
      · have hh : 0 < remaining / 4 * 4 := by omega
        simpa only [hh, ↓reduceIte, chunkPairOffset, Nat.zero_lt_succ, Nat.mul_zero,
          Nat.zero_sub, BitVec.add_zero] using huip
      · rw [hc.sourceReg, hc.completedReg] at hu6
        simpa only [BitVec.ofNat_eq_ofNat] using hu6
      · exact huptr.trans hc.pointerReg
      · intro i hi
        exact hinput i (by omega)
      · simpa only [Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial
    obtain ⟨fuel', t, hchunk, ht⟩ := chunk_result hc boundary hb hlarge huready hucode hf (hucursor.trans hc.cursorSlot) hu0
      (hucompleted.trans hc.completedReg) (husource.trans hc.sourceReg) hinv
    exact ⟨_, t, ha.trans hchunk, ht⟩

end Composition

end Sha3.Proofs.Update.Tail
