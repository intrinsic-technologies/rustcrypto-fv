import Sha3.Proofs.Update.Partial.Context
import Sha3.Proofs.Update.Partial.LoopCode
import Sha3.Proofs.Update.Partial.FillControl

namespace Sha3.Proofs.Update.Partial.Fill

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

section Composition

variable [Bindings] {v : Variant} {pointer source : BitVec 64}
  {position count : Nat} {initial input : Nat → UInt8} {s : RamState}
  (hc : Context v pointer source position count initial input s)
  (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)

include hb in
theorem finish_result {u : RamState} (hr : ReadyToStep u)
    (hcode : CodeIn Extracted.programImage u) (hip : u.RIP = v.updateAddress + 0xe1#64)
    (hframe : AgreesExcept (clobbers pointer position) s u)
    (hpointer : (Operand.reg 15 : Operand 64).read u = pointer)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 count)
    (h3 : (Operand.reg 3 : Operand 64).read u = source)
    (hbytes : Bytes u.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < count then input i else 0))) :
    ∃ t, Advances boundary 2 u t ∧
      FillResult v pointer source position count initial input s t := by
  obtain ⟨t, ha, htready, htcode, htip, ht3, ht7, htframe⟩ :=
    FillControl.finish v boundary hb u hr hcode hip
  refine ⟨t, ha, htready, htcode, htip, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht7.trans hpointer
  · simpa only [h3, h1] using ht3
  · exact (htframe.read (by simp)).trans hpointer
  · simpa only [htframe.external (by simp [Component.Covers])] using hbytes
  · exact frame_trans hframe (htframe.mono (by simp [clobbers]))

include hc hb in
theorem byte_result {u : RamState} (offset : Nat) (hpart : offset + count % 4 = count)
    (hpos : 0 < count % 4) (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hip : u.RIP = v.updateAddress + 0xb8#64)
    (hframe : AgreesExcept (clobbers pointer position) s u)
    (hpointer : (Operand.reg 15 : Operand 64).read u = pointer)
    (h0 : (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 position)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 count)
    (h2 : (Operand.reg 1 : Operand 64).read u = BitVec.ofNat 64 (count % 4))
    (h6 : (Operand.reg 6 : Operand 64).read u = BitVec.ofNat 64 offset)
    (h3 : (Operand.reg 3 : Operand 64).read u = source)
    (hbytes : Bytes u.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0))) :
    ∃ fuel t, Advances boundary fuel u t ∧
      FillResult v pointer source position count initial input s t := by
  obtain ⟨w, ha, hwready, hwcode, hwip, hw0, hw6, hw7, hwframe⟩ :=
    FillControl.byte_setup v boundary hb u hr hcode hip
  have hframew : AgreesExcept (clobbers pointer position) s w :=
    frame_trans hframe (hwframe.mono (by simp [clobbers]))
  have h15 : (Operand.reg 15 : Operand 64).read u = pointer :=
    hpointer
  have hwb : Bytes w.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0)) := by
    simpa only [hwframe.external (by simp [Component.Covers])] using hbytes
  have hinput := hc.sourceBytes_of_frame hframew
  have hspan : offset + count % 4 ≤ 200 - position := by
    have := hc.count_le
    have := v.rate_le
    omega
  have hsrcLow : (source + BitVec.ofNat 64 offset).toNat + count % 4 ≤ 2 ^ 32 := by
    have hl := hc.sourceLow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hinv : ByteInvariant .fill (byteLoopAddress .fill v)
      (source + BitVec.ofNat 64 offset) (destination pointer position)
      offset (count % 4) (200 - position) initial input 0 w := by
    refine ⟨?_, ?_, hw7, ?_, ?_, hinput.sub offset _ (by omega), ?_⟩
    · simpa only [hpos, ↓reduceIte, byteLoopAddress, BitVec.ofNat_eq_ofNat] using hwip
    · exact (hwframe.read (by simp [ByteLoopKind.countReg])).trans h2
    · rw [h6, h3] at hw6
      simpa only [ByteLoopKind.sourceReg, BitVec.add_comm] using hw6
    · rw [h0, h15, h6] at hw0
      simpa only [ByteLoopKind.destinationReg, destination,
        BitVec.add_comm (BitVec.ofNat 64 position) pointer] using hw0
    · simpa only [Nat.add_zero] using hwb
  obtain ⟨x, hloop, hxready, hxcode, hx, hxframe⟩ :=
    byte_loop boundary Extracted.programImage .fill (byteLoopAddress .fill v)
      (source + BitVec.ofNat 64 offset) (destination pointer position)
      offset (count % 4) (200 - position) initial input hspan hsrcLow hc.stateLow
      (by
        intro i hi j hj he
        apply hc.apart i hi (offset + j) (by omega)
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he)
      (fun i hi hp ↦ hc.avoids i hi (Or.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (Or.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (byteBytes_subset .fill v)
      (by
        intro i hi
        apply byte_ne_boundary .fill v boundary hb i
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega) w hwready hwcode hinv
  have hframex : AgreesExcept (clobbers pointer position) s x :=
    frame_trans hframew (hxframe.mono (by simp [byteClobbers, ByteLoopKind.indexReg, clobbers]))
  have hxip : x.RIP = v.updateAddress + 0xe1#64 := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, byteLoopAddress,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hx.rip
  obtain ⟨t, hfinish, ht⟩ := finish_result boundary hb hxready hxcode hxip hframex
    ((hxframe.read (by simp [byteClobbers, ByteLoopKind.indexReg])).trans ((hwframe.read (by simp)).trans hpointer))
    ((hxframe.read (by simp [byteClobbers, ByteLoopKind.indexReg])).trans
      ((hwframe.read (by simp)).trans h1))
    ((hxframe.read (by simp [byteClobbers, ByteLoopKind.indexReg])).trans
      ((hwframe.read (by simp)).trans h3))
    (by simpa only [hpart] using hx.stateBytes)
  exact ⟨_, t, (ha.trans hloop).trans hfinish, ht⟩

include hc hb in
theorem chunk_result {u : RamState}
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hframe : AgreesExcept (clobbers pointer position) s u)
    (hpointer : (Operand.reg 15 : Operand 64).read u = pointer)
    (h0 : (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 position)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 count)
    (h2 : (Operand.reg 1 : Operand 64).read u = BitVec.ofNat 64 (count % 4))
    (hinv : ChunkInvariant (chunkAddress .fill v) source (destination pointer position)
      (4 * (count / 4)) (200 - position) initial input 0 0 u) :
    ∃ fuel t, Advances boundary fuel u t ∧
      FillResult v pointer source position count initial input s t := by
  have hspan : count ≤ 200 - position := by
    have := hc.count_le
    have := v.rate_le
    omega
  obtain ⟨w, ha, hwready, hwcode, hw, hwframe⟩ :=
    chunk_loop boundary Extracted.programImage (chunkAddress .fill v) source
      (destination pointer position) (4 * (count / 4)) (200 - position)
      initial input (by omega) (by have := hc.sourceLow; omega)
      hc.stateLow (fun i hi j hj ↦ hc.apart i hi j (by omega))
      (fun i hi hp ↦ hc.avoids i hi (Or.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (Or.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (chunk_subset .fill v) (chunk_ne_boundary .fill v boundary hb)
      (count / 4) rfl u hr hcode hinv
  have hframew : AgreesExcept (clobbers pointer position) s w :=
    frame_trans hframe (hwframe.mono (by simp [chunkClobbers, clobbers]))
  have hwip : w.RIP = v.updateAddress + 0xb3#64 := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, chunkAddress,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hw.rip
  have hw2 : (Operand.reg 1 : Operand 64).read w = BitVec.ofNat 64 (count % 4) :=
    (hwframe.read (by simp [chunkClobbers])).trans h2
  obtain ⟨x, hxrun, hxready, hxcode, hxip, hxframe⟩ :=
    FillControl.post_chunk v boundary hb w hwready hwcode hwip
  have hframex : AgreesExcept (clobbers pointer position) s x :=
    frame_trans hframew (hxframe.mono (by simp [clobbers]))
  have hxbytes : Bytes x.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < 4 * (count / 4) then input i else 0)) := by
    simpa only [hxframe.external (by simp [Component.Covers]), Nat.add_zero] using hw.stateBytes
  have hx1 : (Operand.reg 2 : Operand 64).read x = BitVec.ofNat 64 count :=
    (hxframe.read (by simp)).trans ((hwframe.read (by simp [chunkClobbers])).trans h1)
  have hx3 : (Operand.reg 3 : Operand 64).read x = source :=
    (hxframe.read (by simp)).trans hw.sourceReg
  rw [hw2] at hxip
  by_cases hzero : count % 4 = 0
  · have hfull : 4 * (count / 4) = count := by omega
    have hxip' : x.RIP = v.updateAddress + 0xe1#64 := by
      simpa only [hzero, BitVec.ofNat_eq_ofNat, ↓reduceIte] using hxip
    obtain ⟨t, hfinish, ht⟩ := finish_result boundary hb hxready hxcode hxip' hframex
      ((hxframe.read (by simp)).trans ((hwframe.read (by simp [chunkClobbers])).trans hpointer)) hx1 hx3 (by simpa only [hfull] using hxbytes)
    exact ⟨_, t, (ha.trans hxrun).trans hfinish, ht⟩
  · have hz : BitVec.ofNat 64 (count % 4) ≠ 0#64 := by
      intro he
      have he' := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at he'
      omega
    have hxip' : x.RIP = v.updateAddress + 0xb8#64 := by
      simpa only [BitVec.ofNat_eq_ofNat, hz, ↓reduceIte] using hxip
    obtain ⟨fuel, t, htail, ht⟩ := byte_result hc boundary hb (4 * (count / 4))
      (by omega) (by omega) hxready hxcode hxip' hframex
      ((hxframe.read (by simp)).trans ((hwframe.read (by simp [chunkClobbers])).trans hpointer))
      ((hxframe.read (by simp)).trans ((hwframe.read (by simp [chunkClobbers])).trans h0))
      hx1 ((hxframe.read (by simp)).trans hw2)
      ((hxframe.read (by simp)).trans hw.indexReg) hx3 hxbytes
    exact ⟨_, t, (ha.trans hxrun).trans htail, ht⟩

include hc hb in
theorem advance (hposition : 0 < position) (hcount : count = v.rate - position)
    (hip : s.RIP = v.updateAddress + 0x64#64)
    (hcf : condHolds 3#4 (StatusFlags.ofRFLAGS s.RFLAGS) = decide (4 ≤ count))
    (hrem : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 (count % 4))
    (hcountreg : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 count) :
    ∃ fuel t, Advances boundary fuel s t ∧
      FillResult v pointer source position count initial input s t := by
  obtain ⟨u, ha, huready, hucode, huip, huframe⟩ :=
    FillControl.dispatch_branch v boundary hb s hc.ready hc.code hip
  rw [hcf] at huip
  simp only [decide_eq_true_eq] at huip
  have hu2 : (Operand.reg 1 : Operand 64).read u = BitVec.ofNat 64 (count % 4) :=
    (huframe.read (by simp)).trans hrem
  have hupointer : (Operand.reg 15 : Operand 64).read u = pointer :=
    (huframe.read (by simp)).trans hc.pointerReg
  have hf : AgreesExcept (clobbers pointer position) s u :=
    huframe.mono (by simp [clobbers])
  have huinitial : Bytes u.external (destination pointer position) (200 - position) initial := by
    simpa only [huframe.external (by simp [Component.Covers])] using hc.stateBytes
  have hu0 : (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 position :=
    (huframe.read (by simp)).trans hc.positionReg
  have hu1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 count :=
    (huframe.read (by simp)).trans hcountreg
  have hu3 : (Operand.reg 3 : Operand 64).read u = source :=
    (huframe.read (by simp)).trans hc.sourceReg
  by_cases hlarge : 4 ≤ count
  · have hlt : count < 145 := by
      have hrate : v.rate ≤ 144 := by cases v <;> decide
      omega
    obtain ⟨w, hwrun, hwready, hwcode, hwip, hw7, hw6, hw8, hwframe⟩ :=
      FillControl.chunk_setup v boundary hb u ⟨count, hlt⟩ huready hucode
        (by simpa only [hlarge, ↓reduceIte] using huip) hu1
    have hframew : AgreesExcept (clobbers pointer position) s w :=
      frame_trans hf (hwframe.mono (by simp [clobbers]))
    have hinput := hc.sourceBytes_of_frame hframew
    have hinv : ChunkInvariant (chunkAddress .fill v) source (destination pointer position)
        (4 * (count / 4)) (200 - position) initial input 0 0 w := by
      refine ⟨?_, hw7, hw6, (hwframe.read (by simp)).trans hu3, ?_, ?_, ?_⟩
      · have hh : 0 < 4 * (count / 4) := by omega
        simpa only [hh, ↓reduceIte, chunkAddress, chunkPairOffset, Nat.zero_lt_succ,
          Nat.mul_zero, Nat.zero_sub, BitVec.add_zero, BitVec.ofNat_eq_ofNat] using hwip
      · rw [hu0, hupointer] at hw8
        simpa only [destination, BitVec.ofNat_eq_ofNat,
          BitVec.add_comm (BitVec.ofNat 64 position) pointer] using hw8
      · intro i hi
        exact hinput i (by omega)
      · simpa only [hwframe.external (by simp [Component.Covers]), Nat.add_zero,
          Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial
    obtain ⟨fuel, t, hchunk, ht⟩ := chunk_result hc boundary hb hwready hwcode hframew
      ((hwframe.read (by simp)).trans hupointer)
      ((hwframe.read (by simp)).trans hu0) ((hwframe.read (by simp)).trans hu1)
      ((hwframe.read (by simp)).trans hu2) hinv
    exact ⟨_, t, (ha.trans hwrun).trans hchunk, ht⟩
  · have hsmall : count < 4 := by omega
    have hmod : count % 4 = count := Nat.mod_eq_of_lt hsmall
    have hpos : 0 < count % 4 := by have := hc.position_lt; omega
    obtain ⟨w, hwrun, hwready, hwcode, hwip, hw6, hwframe⟩ :=
      FillControl.small_setup v boundary hb u huready hucode
        (by simpa only [hlarge, ↓reduceIte] using huip)
    have hframew : AgreesExcept (clobbers pointer position) s w :=
      frame_trans hf (hwframe.mono (by simp [clobbers]))
    obtain ⟨fuel, t, htail, ht⟩ := byte_result hc boundary hb 0 (by omega) hpos
      hwready hwcode hwip hframew ((hwframe.read (by simp)).trans hupointer)
      ((hwframe.read (by simp)).trans hu0)
      ((hwframe.read (by simp)).trans hu1) ((hwframe.read (by simp)).trans hu2)
      hw6 ((hwframe.read (by simp)).trans hu3)
      (by simpa only [hwframe.external (by simp [Component.Covers]),
        Nat.not_lt_zero, ↓reduceIte, UInt8.xor_zero] using huinitial)
    exact ⟨_, t, (ha.trans hwrun).trans htail, ht⟩

end Composition

end Sha3.Proofs.Update.Partial.Fill
