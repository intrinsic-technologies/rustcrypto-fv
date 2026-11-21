import Sha3.Proofs.Incremental.Chunks
import Sha3.Proofs.LaneMemory

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs

theorem bytes_patch_suffix {s t : RamState} {base : BitVec 64} {total position : Nat}
    {initial localBytes : Nat → UInt8} (hposition : position ≤ total)
    (hinitial : Bytes s.external base total initial)
    (hlocal : Bytes t.external (base + BitVec.ofNat 64 position)
      (total - position) localBytes)
    (hunchanged : ∀ i < position,
      t.external[base + BitVec.ofNat 64 i]? = s.external[base + BitVec.ofNat 64 i]?) :
    Bytes t.external base total
      (fun i ↦ if i < position then initial i else localBytes (i - position)) := by
  have hprefix : Bytes t.external base position initial := by
    intro i hi
    rw [hunchanged i hi]
    exact hinitial i (by omega)
  simpa only [Nat.add_sub_cancel' hposition] using hprefix.append hlocal

theorem bytes_patch_suffix_of_agreesExcept {s t : RamState} {base : BitVec 64}
    {total position : Nat} {initial localBytes : Nat → UInt8} {components : List Component}
    (hposition : position ≤ total) (htotal : total ≤ 2 ^ 64)
    (hinitial : Bytes s.external base total initial)
    (hlocal : Bytes t.external (base + BitVec.ofNat 64 position)
      (total - position) localBytes)
    (hframe : AgreesExcept components s t)
    (hcovers : ∀ c ∈ components, ∀ address, c.Covers address →
      (Component.mem (base + BitVec.ofNat 64 position) (total - position)).Covers address) :
    Bytes t.external base total
      (fun i ↦ if i < position then initial i else localBytes (i - position)) := by
  apply bytes_patch_suffix hposition hinitial hlocal
  intro i hi
  apply hframe.byte
  intro c hc hcover
  obtain ⟨j, hj, he⟩ := hcovers c hc _ hcover
  have hapart := RangeApart.offsets base (a := position) (len := total - position)
    (b := 0) (count := position) (by omega) (by omega) (.inr (by omega))
  exact hapart j hj i hi (by simpa only [BitVec.add_zero] using he.symm)

theorem bytes_xor_slice_of_patch {t : RamState} {base : BitVec 64}
    {total position : Nat} {initial : Nat → UInt8} (bytes : ByteArray)
    (hbytes : Bytes t.external base total (fun i ↦ if i < position then initial i else
      initial (position + (i - position)) ^^^
        (if i - position < bytes.size then (bytes.data[i - position]?).getD 0 else 0))) :
    Bytes t.external base total
      (fun i ↦ initial i ^^^
        (if position ≤ i ∧ i - position < bytes.size then
          (bytes.data[i - position]?).getD 0 else 0)) := by
  apply hbytes.congr
  intro i _
  by_cases hi : i < position
  · have hnot : ¬position ≤ i := by omega
    simp only [hi, ↓reduceIte, hnot, false_and, UInt8.xor_zero]
  · have hle : position ≤ i := by omega
    simp only [hi, ↓reduceIte, Nat.add_sub_cancel' hle, hle, true_and]

theorem exists_memoryLanes_bytes {s : RamState} {base : BitVec 64}
    (lanes : Keccak.Lanes) (hread : MemReadable s base 200)
    (hlanes : Permutation.memoryLanes base s = lanes) :
    ∃ initial : Nat → UInt8, Bytes s.external base 200 initial ∧
      ∀ lane : Fin 25, ∀ j : Fin 8,
        initial (8 * lane.val + j.val) = storedByte (lanes lane) j.val := by
  refine ⟨fun i ↦ memByte s.external (base + BitVec.ofNat 64 i),
    Bytes.of_isSome hread.mem, ?_⟩
  intro lane j
  rw [← hlanes]
  exact (LaneMemory.storedByte_memoryLanes base s lane j).symm

theorem memoryLanes_xor_slice {t : RamState} {base : BitVec 64}
    (lanes : Keccak.Lanes) (position : Nat) (bytes : ByteArray)
    (initial : Nat → UInt8)
    (hvalues : ∀ lane : Fin 25, ∀ j : Fin 8,
      initial (8 * lane.val + j.val) = storedByte (lanes lane) j.val)
    (hbytes : Bytes t.external base 200
      (fun i ↦ initial i ^^^
        (if position ≤ i ∧ i - position < bytes.size then
          (bytes.data[i - position]?).getD 0 else 0))) :
    Permutation.memoryLanes base t =
      fun lane ↦ lanes lane ^^^ Incremental.sliceLanes position bytes lane := by
  apply LaneMemory.memoryLanes_eq_of_byteFunction base t _ _ hbytes
  intro lane j
  rw [storedByte_xor, hvalues,
    storedByte_eq_extract (Incremental.sliceLanes position bytes lane),
    Incremental.sliceLanes_extract_byte]
  by_cases hi : position ≤ 8 * lane.val + j.val ∧
      8 * lane.val + j.val - position < bytes.size
  · simp only [hi, and_self, ↓reduceIte, ↓reduceDIte,
      Array.getElem?_eq_getElem hi.2, Option.getD_some]
  · simp only [hi, ↓reduceIte, ↓reduceDIte]

end Sha3.Proofs.Update.Partial
