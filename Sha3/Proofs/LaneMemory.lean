import Sha3.Proofs.Absorption
import Sha3.Proofs.Permutation.Layout
import X86Proofs.Program.ReadWrite.Bytes
import Sha3.Proofs.Outcome

namespace Sha3.Proofs.LaneMemory

open X86 X86.Machine X86Proofs Prelude Sha3.Spec Sha3.Spec.Program
open Keccak Absorption Permutation

theorem memoryLanes_eq_of_memByte_eq {s t : RamState} (pointer : BitVec 64)
    (h : ∀ address, memByte s.external address = memByte t.external address) :
    memoryLanes pointer s = memoryLanes pointer t := by
  unfold memoryLanes
  funext lane
  simp only [Operand.read]
  exact memLoad_congr (fun _ _ ↦ h _)

theorem getElem_digestLanes_eq_storedByte (a : Lanes) (n : Nat) (hn : n ≤ 200)
    (i : Nat) (hi : i < n) :
    (digestLanes a n hn)[i] = storedByte (a ⟨i / 8, by omega⟩) (i % 8) := by
  simp only [digestLanes, Vector.getElem_ofFn, storedByte_eq_extract]

theorem storedByte_memoryLanes (pointer : BitVec 64) (s : RamState)
    (lane : Fin 25) (j : Fin 8) :
    storedByte (memoryLanes pointer s lane) j.val =
      memByte s.external (pointer + BitVec.ofNat 64 (8 * lane.val + j.val)) := by
  change storedByte (memLoad s.external (pointer + BitVec.ofNat 64 (8 * lane.val)) 64)
    j.val = _
  rw [storedByte_memLoad _ _ _ j.isLt, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memoryLanes_eq_of_bytes (pointer : BitVec 64) (s : RamState) (a : Lanes)
    (hbytes : ∀ lane : Fin 25, ∀ j : Fin 8,
      s.external[pointer + BitVec.ofNat 64 (8 * lane.val + j.val)]? =
        some (storedByte (a lane) j.val)) : memoryLanes pointer s = a := by
  funext lane
  change memLoad s.external (pointer + BitVec.ofNat 64 (8 * lane.val)) 64 = a lane
  apply Bytes.memLoad (n := 64) (hn := by decide) (h128 := by decide)
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hbytes lane ⟨j, hj⟩

theorem memoryLanes_eq_of_byteFunction (pointer : BitVec 64) (s : RamState)
    (a : Lanes) (bytes : Nat → UInt8) (hbytes : Bytes s.external pointer 200 bytes)
    (hvalues : ∀ lane : Fin 25, ∀ j : Fin 8,
      bytes (8 * lane.val + j.val) = storedByte (a lane) j.val) :
    memoryLanes pointer s = a := by
  apply memoryLanes_eq_of_bytes
  intro lane j
  rw [← hvalues]
  exact hbytes _ (by omega)

theorem bytesAt_of_hasBytes {s : RamState} {region : MemoryRegion} {input : ByteArray}
    (h : region.HasBytes s.external input) :
    BytesAt s (BitVec.ofNat 64 region.start) input.data.toList := by
  intro i hi
  have hb := h.2 ⟨i, by simpa only [ByteArray.size, Array.length_toList] using hi⟩
  rw [BitVec.ofNat_add] at hb
  exact hb

theorem bytesAt_of_validInputSlice {s : RamState} {inputs : Array Input} {i : Fin inputs.size}
    (h : ValidInputSlice s inputs i) : BytesAt s inputs[i].address inputs[i].bytes.data.toList := by
  have hb := bytesAt_of_hasBytes h.2.2.2.2
  simpa only [Input.region, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

theorem memLoad_blockLanes_of_bytesAt {s : RamState} {pointer : BitVec 64}
    {input : ByteArray} (hbytes : BytesAt s pointer input.data.toList)
    (offset rate : Nat) (lane : Fin 25) (hlane : 8 * (lane.val + 1) ≤ rate)
    (hread : offset + 8 * (lane.val + 1) ≤ input.size) :
    memLoad s.external (pointer + BitVec.ofNat 64 (offset + 8 * lane.val)) 64 =
      blockLanes input offset rate lane := by
  apply Bytes.memLoad (n := 64) (hn := by decide) (h128 := by decide)
  intro j hj
  have hr : 8 * lane.val + j < rate := by omega
  have hi : offset + (8 * lane.val + j) < input.size := by omega
  rw [storedByte_eq_extract, blockLanes_extract_byte input offset rate lane ⟨j, hj⟩]
  simp only [hr, hi, and_self, ↓reduceDIte]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  exact hbytes (offset + (8 * lane.val + j)) (by simpa using hi)

theorem memoryLanes_write_lane (pointer : BitVec 64) (s : RamState)
    (lane : Fin 25) (v : BitVec 64) :
    memoryLanes pointer ((Operand.mem (pointer + BitVec.ofNat 64 (8 * lane.val)) :
      Operand 64).write s v) = setLane (memoryLanes pointer s) lane v := by
  funext k
  by_cases hk : k = lane
  · subst k
    simp only [setLane, ↓reduceIte, memoryLanes, Operand.read, Operand.write]
    exact memLoad_memStore _ _ (by decide) (by decide) v
  · simp only [setLane, hk, ↓reduceIte, memoryLanes, Operand.read, Operand.write]
    apply memLoad_congr
    intro j hj
    simp only [memByte, PhysicalMemory.read]
    rw [memStore_getElem?_of_ne]
    intro i hi he
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at he
    have haddr := congrArg BitVec.toNat ((BitVec.add_right_inj pointer).mp he)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * lane.val + i < 2^64 by omega),
      Nat.mod_eq_of_lt (show 8 * k.val + j < 2^64 by omega)] at haddr
    apply hk
    apply Fin.ext
    omega

theorem storedByte_blockLanes_final (rate : Nat) (input : ByteArray) (hr : 0 < rate)
    (lane : Fin 25) (j : Fin 8) :
    let index := 8 * lane.val + j.val
    storedByte (blockLanes (paddedBytes rate input) (input.size / rate * rate) rate lane) j.val =
      (((if index < input.size % rate then
          (input.data[input.size / rate * rate + index]?).getD 0 else 0) ^^^
        ((if index = input.size % rate then 0x06 else 0) : UInt8)) ^^^
        ((if index + 1 = rate then 0x80 else 0) : UInt8)) := by
  dsimp only
  rw [storedByte_eq_extract, blockLanes_extract_byte]
  have hmod := Nat.mod_lt input.size hr
  by_cases hj : 8 * lane.val + j.val < rate
  · have hread : input.size / rate * rate + (8 * lane.val + j.val) <
        (paddedBytes rate input).size := by
      rw [size_paddedBytes rate input hr]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    simp only [hj, hread, and_self, ↓reduceDIte]
    rw [getElem_paddedBytes_final rate input hr _ hj]
    by_cases hrem : 8 * lane.val + j.val < input.size % rate
    · have hinput : input.size / rate * rate + (8 * lane.val + j.val) < input.data.size := by
        have hd := Nat.div_add_mod input.size rate
        rw [Nat.mul_comm rate] at hd
        change _ < input.size
        omega
      simp only [hrem, ↓reduceDIte, ↓reduceIte, Array.getElem?_eq_getElem hinput,
        Option.getD_some]
    · simp [hrem]
  · have hrem : ¬8 * lane.val + j.val < input.size % rate := by omega
    have hfirst : ¬8 * lane.val + j.val = input.size % rate := by omega
    have hlast : ¬8 * lane.val + j.val + 1 = rate := by omega
    simp [hj, hrem, hfirst, hlast]

theorem memByte_eq_digestLanes_of_chunkLoads (m : Ram) (base : BitVec 64) (a : Lanes)
    (n : Nat) (hn : n ≤ 200)
    (hloads : ∀ k (hk : 8 * k < n),
      memLoad m (base + BitVec.ofNat 64 (8 * k)) (8 * min 8 (n - 8 * k)) =
        (a ⟨k, by omega⟩).setWidth (8 * min 8 (n - 8 * k)))
    (i : Nat) (hi : i < n) :
    memByte m (base + BitVec.ofNat 64 i) = (Absorption.digestLanes a n hn)[i] := by
  have hk : 8 * (i / 8) < n := by omega
  have hbyte : i % 8 < (8 * min 8 (n - 8 * (i / 8))) / 8 := by omega
  have h := storedByte_memLoad m (base + BitVec.ofNat 64 (8 * (i / 8))) (i % 8) hbyte
  rw [hloads (i / 8) hk] at h
  have haddress : base + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      base + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [haddress] at h
  rw [← h]
  simp only [Absorption.digestLanes, Vector.getElem_ofFn, storedByte_eq_extract]
  rw [BitVec.extractLsb'_setWidth_of_le (by omega)]

theorem readBytes_eq_digestLanes_of_chunkLoads {initial final : RamState} {entry : Routine}
    (output : Routine → RamState → MemoryRegion)
    (a : Lanes) (hn : entry.outputBytes ≤ 200)
    (halloc : ∀ i < entry.outputBytes,
      (final.external[BitVec.ofNat 64 ((output entry initial).start) + BitVec.ofNat 64 i]?).isSome)
    (hloads : ∀ k (hk : 8 * k < entry.outputBytes),
      memLoad final.external (BitVec.ofNat 64 ((output entry initial).start) + BitVec.ofNat 64 (8 * k))
          (8 * min 8 (entry.outputBytes - 8 * k)) =
        (a ⟨k, by omega⟩).setWidth (8 * min 8 (entry.outputBytes - 8 * k))) :
    readBytes (output entry initial) entry.outputBytes final =
      .ok (Absorption.digestLanes a entry.outputBytes hn) := by
  apply readBytes_eq_of_bytes
  intro i
  have h := Bytes.of_isSome halloc i.val i.isLt
  dsimp only at h
  rw [memByte_eq_digestLanes_of_chunkLoads _ _ a _ hn hloads i.val i.isLt] at h
  simpa only [BitVec.ofNat_add] using h

theorem readBytes_sha3_224_eq_digestLanes {initial final : RamState}
    (output : Routine → RamState → MemoryRegion) (a : Lanes)
    (halloc : ∀ i < 28,
      (final.external[BitVec.ofNat 64 ((output sha3_224_digest_slices initial).start) + BitVec.ofNat 64 i]?).isSome)
    (hloads64 : ∀ k (hk : k < 3),
      memLoad final.external
        (BitVec.ofNat 64 ((output sha3_224_digest_slices initial).start) + BitVec.ofNat 64 (8 * k)) 64 =
        a ⟨k, by omega⟩)
    (hload32 : memLoad final.external (BitVec.ofNat 64 ((output sha3_224_digest_slices initial).start) + 24) 32 =
      (a ⟨3, by decide⟩).setWidth 32) :
    readBytes (output sha3_224_digest_slices initial) 28 final =
      .ok (Absorption.digestLanes a 28 (by decide)) := by
  apply readBytes_eq_digestLanes_of_chunkLoads output a (by decide) halloc
  intro k hk
  change 8 * k < 28 at hk
  change memLoad final.external
      (BitVec.ofNat 64 ((output sha3_224_digest_slices initial).start) + BitVec.ofNat 64 (8 * k))
      (8 * min 8 (28 - 8 * k)) = (a ⟨k, _⟩).setWidth (8 * min 8 (28 - 8 * k))
  by_cases hk3 : k < 3
  · have hcount : min 8 (28 - 8 * k) = 8 := by omega
    rw [hcount]
    exact hloads64 k hk3
  · have hk3 : k = 3 := by omega
    subst k
    exact hload32

end Sha3.Proofs.LaneMemory
