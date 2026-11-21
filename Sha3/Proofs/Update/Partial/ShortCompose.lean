import Sha3.Proofs.Update.Partial.ShortLoops
import Sha3.Proofs.Update.Partial.ShortDispatch

namespace Sha3.Proofs.Update.Partial.Short

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

section Composition

variable [Bindings] {v : Variant} {pointer source : BitVec 64}
  {position count : Nat} {initial input : Nat → UInt8} {s : RamState}
  (hc : Context v pointer source position count initial input s)
  (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)

include hc hb in
theorem byte_result {u : RamState} (offset : Nat)
    (hpart : offset + count % 4 = count) (hpos : 0 < count % 4)
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hip : u.RIP = byteSetupPC v)
    (hframe : AgreesExcept (workClobbers pointer position) s u)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 (count % 4))
    (hpointer : (Operand.reg 15 : Operand 64).read u = pointer)
    (h6 : (Operand.reg 6 : Operand 64).read u = BitVec.ofNat 64 offset)
    (h3 : (Operand.reg 3 : Operand 64).read u = source)
    (hbytes : Bytes u.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0))) :
    ∃ fuel t, Advances boundary fuel u t ∧
      WorkResult v pointer position count initial input s t := by
  obtain ⟨w, ha, hwready, hwcode, _, hwip, hwframe, hw7, hw3, hw6⟩ :=
    byte_setup v u hr hcode hb hip
  have hframew : AgreesExcept (workClobbers pointer position) s w :=
    workFrame_trans hframe (hwframe.mono (by simp [workClobbers]))
  have hw1 : (Operand.reg 2 : Operand 64).read w = BitVec.ofNat 64 (count % 4) :=
    (hwframe.read (by simp)).trans h1
  have hw7' : (Operand.reg 15 : Operand 64).read w =
      destination pointer position + BitVec.ofNat 64 offset := by
    have h15 := hpointer
    have h0 := (hframe.read (n := 64) (r := 0) (by simp [workClobbers])).trans hc.positionReg
    rw [h15, h6, h0] at hw7
    rw [hw7]
    simp only [destination, BitVec.add_assoc]
    rw [BitVec.add_comm (BitVec.ofNat 64 offset) (BitVec.ofNat 64 position)]
  have hw3' : (Operand.reg 3 : Operand 64).read w = source + BitVec.ofNat 64 offset := by
    simpa only [h3, h6] using hw3
  have hwb : Bytes w.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0)) := by
    simpa only [hwframe.external (by simp [Component.Covers])] using hbytes
  obtain ⟨t, hloop, ht⟩ := byte_loop_result hc boundary hb offset hpart hpos
    hwready hwcode hwip hframew hw1 hw6 hw7' hw3' hwb
  exact ⟨_, t, ha.trans hloop, ht⟩

include hc hb in
theorem chunk_result {u : RamState}
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hframe : AgreesExcept (workClobbers pointer position) s u)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 (count % 4))
    (hpointer : (Operand.reg 15 : Operand 64).read u = pointer)
    (hinv : ChunkInvariant (chunkAddress .short v) source (destination pointer position)
      (count / 4 * 4) (200 - position) initial input 0 0 u) :
    ∃ fuel t, Advances boundary fuel u t ∧
      WorkResult v pointer position count initial input s t := by
  obtain ⟨w, ha, hwready, hwcode, hw, hframew, hwframe⟩ :=
    chunk_loop_result hc boundary hb hr hcode hframe hinv
  have hwip : w.RIP = chunkSetupPC v + 78#64 := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, chunkAddress, chunkPC,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hw.rip
  have hw1 : (Operand.reg 2 : Operand 64).read w = BitVec.ofNat 64 (count % 4) :=
    (hwframe.read (by simp [chunkClobbers])).trans h1
  obtain ⟨x, hxrun, hxready, hxcode, _, hxip, hxobs, hxframe⟩ :=
    postchunk_test v w hwready hwcode hb hwip
  have hframex : AgreesExcept (workClobbers pointer position) s x :=
    workFrame_trans hframew (hxframe.mono (by simp [workClobbers]))
  have hxbytes : Bytes x.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < count / 4 * 4 then input i else 0)) := by
    simpa only [hxframe.external (by simp [Component.Covers]), Nat.add_zero] using hw.stateBytes
  rw [hw1] at hxip
  simp only [BitVec.ofNat_eq_ofNat] at hxip
  by_cases hzero : count % 4 = 0
  · have hfull : count / 4 * 4 = count := by omega
    have hxip' : x.RIP = addPC v := by
      simpa only [hzero, BitVec.ofNat_eq_ofNat, beq_self_eq_true, ↓reduceIte] using hxip
    exact ⟨_, x, ha.trans hxrun, hxready, hxcode, hxip',
      by simpa only [hfull] using hxbytes, hframex⟩
  · have hz : (BitVec.ofNat 64 (count % 4) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      have he' := congrArg BitVec.toNat (eq_of_beq he)
      simp only [BitVec.toNat_ofNat] at he'
      omega
    have hxip' : x.RIP = byteSetupPC v := by
      simpa only [hz, Bool.false_eq_true, ↓reduceIte] using hxip
    obtain ⟨fuel, t, htail, ht⟩ := byte_result hc boundary hb (count / 4 * 4)
      (by omega) (by omega) hxready hxcode hxip' hframex
      ((hxobs.read_reg _).symm.trans hw1)
      ((hxobs.read_reg _).symm.trans ((hwframe.read (by simp [chunkClobbers])).trans hpointer))
      ((hxobs.read_reg _).symm.trans hw.indexReg)
      ((hxobs.read_reg _).symm.trans hw.sourceReg) hxbytes
    exact ⟨_, t, (ha.trans hxrun).trans htail, ht⟩

include hc hb in
theorem work_advance (hcount : count < 200)
    (hip : s.RIP = v.updateAddress + 0x29#64)
    (hlen : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 count) :
    ∃ fuel t, Advances boundary fuel s t ∧
      WorkResult v pointer position count initial input s t := by
  obtain ⟨u, ha, huready, hucode, _, huip, huobs, huframe⟩ :=
    entry_test v s hc.ready hc.code hb hip
  have hframeu : AgreesExcept (workClobbers pointer position) s u :=
    huframe.mono (by simp [workClobbers])
  have huinitial : Bytes u.external (destination pointer position) (200 - position) initial := by
    simpa only [huframe.external (by simp [Component.Covers])] using hc.stateBytes
  rw [hlen] at huip
  simp only [BitVec.ofNat_eq_ofNat] at huip
  by_cases hzero : count = 0
  · have huip' : u.RIP = addPC v := by
      simpa only [hzero, BitVec.ofNat_eq_ofNat, beq_self_eq_true, ↓reduceIte] using huip
    refine ⟨_, u, ha, huready, hucode, huip', ?_, hframeu⟩
    simpa only [hzero, Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial
  · have hz : (BitVec.ofNat 64 count == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      have he' := congrArg BitVec.toNat (eq_of_beq he)
      simp only [BitVec.toNat_ofNat] at he'
      omega
    have huip' : u.RIP = v.updateAddress + 0x32#64 := by
      simpa only [hz, Bool.false_eq_true, ↓reduceIte] using huip
    obtain ⟨w, hdispatch, hwready, hwcode, _, hwip, hw1, hwframe⟩ :=
      dispatch_compare v ⟨count, hcount⟩ u huready hucode hb huip'
        ((huobs.read_reg _).symm.trans hlen)
    have hframew : AgreesExcept (workClobbers pointer position) s w :=
      workFrame_trans hframeu (hwframe.mono (by simp [workClobbers]))
    have hwinitial : Bytes w.external (destination pointer position) (200 - position) initial := by
      simpa only [hwframe.external (by simp [Component.Covers])] using huinitial
    have hw3 : (Operand.reg 3 : Operand 64).read w = source :=
      (hwframe.read (by simp)).trans ((huobs.read_reg _).symm.trans hc.sourceReg)
    by_cases hlarge : 4 ≤ count
    · have hwip' : w.RIP = chunkSetupPC v := by
        simpa only [hlarge, ↓reduceIte] using hwip
      have hw2 : (Operand.reg 1 : Operand 64).read w = BitVec.ofNat 64 count :=
        (hwframe.read (by simp)).trans ((huobs.read_reg _).symm.trans hlen)
      obtain ⟨x, hsetup, hxready, hxcode, _, hxip, hx7, hx6, hx8, hxframe⟩ :=
        chunk_setup v ⟨count, hcount⟩ w hwready hwcode hb hwip' hw2
      have hframex : AgreesExcept (workClobbers pointer position) s x :=
        workFrame_trans hframew (hxframe.mono (by simp [workClobbers]))
      have hxinitial : Bytes x.external (destination pointer position) (200 - position) initial := by
        simpa only [hxframe.external (by simp [Component.Covers])] using hwinitial
      have hinv : ChunkInvariant (chunkAddress .short v) source (destination pointer position)
          (count / 4 * 4) (200 - position) initial input 0 0 x := by
        refine ⟨?_, hx7, hx6, (hxframe.read (by simp)).trans hw3, ?_, ?_, ?_⟩
        · have hp : 0 < count / 4 * 4 := by omega
          simpa only [chunkPairOffset, Nat.mul_zero, Nat.zero_sub, Nat.zero_lt_succ,
            ↓reduceIte, hp, BitVec.ofNat_eq_ofNat, BitVec.add_zero, chunkAddress] using hxip
        · have hw0 := (hframew.read (n := 64) (r := 0) (by simp [workClobbers])).trans hc.positionReg
          have hw15 := (hwframe.read (n := 64) (r := 15) (by simp)).trans ((huobs.read_reg _).symm.trans hc.pointerReg)
          rw [hw0, hw15] at hx8
          simpa only [destination, BitVec.add_comm (BitVec.ofNat 64 position) pointer,
            BitVec.ofNat_eq_ofNat] using hx8
        · intro i hi
          exact hc.sourceBytes_of_frame (workFrame_mono hframex) i (by omega)
        · simpa only [Nat.zero_add, Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using hxinitial
      obtain ⟨fuel, t, hrest, ht⟩ := chunk_result hc boundary hb hxready hxcode hframex
        ((hxframe.read (by simp)).trans hw1)
        ((hxframe.read (by simp)).trans ((hwframe.read (by simp)).trans ((huobs.read_reg _).symm.trans hc.pointerReg))) hinv
      exact ⟨_, t, (ha.trans (hdispatch.trans hsetup)).trans hrest, ht⟩
    · have hwip' : w.RIP = v.updateAddress + 0x41#64 := by
        simpa only [hlarge, ↓reduceIte] using hwip
      obtain ⟨x, hsetup, hxready, hxcode, _, hxip, hx6, hxframe⟩ :=
        short_setup v w hwready hwcode hb hwip'
      have hframex : AgreesExcept (workClobbers pointer position) s x :=
        workFrame_trans hframew (hxframe.mono (by simp [workClobbers]))
      have hxinitial : Bytes x.external (destination pointer position) (200 - position)
          (fun i ↦ initial i ^^^ (if i < 0 then input i else 0)) := by
        simpa only [hxframe.external (by simp [Component.Covers]), Nat.not_lt_zero,
          ↓reduceIte, UInt8.xor_zero] using hwinitial
      obtain ⟨fuel, t, hrest, ht⟩ := byte_result hc boundary hb 0
        (by omega) (by omega) hxready hxcode hxip hframex
        ((hxframe.read (by simp)).trans hw1)
        ((hxframe.read (by simp)).trans ((hwframe.read (by simp)).trans ((huobs.read_reg _).symm.trans hc.pointerReg))) hx6
        ((hxframe.read (by simp)).trans hw3) hxinitial
      exact ⟨_, t, (ha.trans (hdispatch.trans hsetup)).trans hrest, ht⟩

include hc hb in
theorem advance (hshort : position + count < v.rate)
    (hip : s.RIP = v.updateAddress + 0x29#64)
    (hlen : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 count) :
    ∃ fuel t, Advances boundary fuel s t ∧
      ShortResult v pointer position count initial input s t := by
  have hsum : position + count < 200 := Nat.lt_of_lt_of_le hshort v.rate_le
  obtain ⟨fuel, u, ha, hu⟩ := work_advance hc boundary hb (by omega) hip hlen
  have hu0 := (hu.frame.read (n := 64) (r := 0) (by simp [workClobbers])).trans hc.positionReg
  have hu2 := (hu.frame.read (n := 64) (r := 1) (by simp [workClobbers])).trans hlen
  obtain ⟨t, ht, htready, htcode, htip, ht2, htframe⟩ :=
    cursor_advance v position count hsum u hu.ready hu.code hb hu.rip hu0 hu2
  refine ⟨_, t, ha.trans ht, htready, htcode, htip, ht2, ?_, ?_, ?_⟩
  · exact (htframe.read (by simp)).trans (hu.frame.read (by simp [workClobbers]))
  · simpa only [htframe.external (by simp [Component.Covers])] using hu.stateBytes
  · exact (hu.frame.trans htframe).mono (by simp [workClobbers, Partial.clobbers])

end Composition

end Sha3.Proofs.Update.Partial.Short
