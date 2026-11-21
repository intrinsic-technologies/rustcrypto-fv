import P256.Spec
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem readLength_of_bytes {s : RamState} {base : BitVec 64} {value : BitVec 64}
    (h : Bytes s.external base 8 (storedByte value)) :
    (List.range 8).foldrM
      (fun i n => do return n * 256 + (← readByte s (base.toNat + i)).toNat) 0 =
      Except.ok (ε := Fault) value.toNat := by
  have hb (i : Nat) (hi : i < 8) :
      readByte s (base.toNat + i) = .ok (storedByte value i) := by
    simp only [readByte, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, h i hi]
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide)
  have h7 := hb 7 (by decide)
  rw [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl]
  simp only [List.foldrM_cons, List.foldrM_nil, h0, h1, h2, h3, h4, h5, h6, h7,
    pure, bind, Except.bind, Except.pure, storedByte, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow]
  congr 1
  have := value.isLt
  omega

theorem readBytes_of_bytes {s : RamState} {start : Nat} {bytes : ByteArray}
    (h : ∀ i < bytes.size,
      readByte s (start + i) = .ok bytes.data[i]!) :
    (List.range bytes.size).mapM (fun i => readByte s (start + i)) =
      Except.ok bytes.data.toList := by
  have hm (is : List Nat) (hi : ∀ i ∈ is, i < bytes.size) :
      is.mapM (fun i => readByte s (start + i)) =
        Except.ok (is.map (fun i => bytes.data[i]!)) := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      have hi0 := hi i (by simp)
      rw [List.mapM_cons, h i hi0, ih (fun j hj => hi j (by simp [hj]))]
      rfl
  rw [hm _ (by simpa only [List.mem_range] using fun i hi => hi)]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, Array.length_toList, ByteArray.size_data]
  · intro i hi hj
    have hib : i < bytes.data.size := by simpa only [Array.length_toList] using hj
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, getElem!_pos bytes.data i hib]

theorem bytes_of_memLoad_eq {source final : RamState} {src dst : BitVec 64}
    {count : Nat} {bytes : ByteArray}
    (hinput : (MemoryRegion.mk src.toNat (8 * count)).HasBytes source.external bytes)
    (hallocated : ∀ i < 8 * count, (final.external[dst + BitVec.ofNat 64 i]?).isSome)
    (hread : ∀ j < count, memLoad final.external (dst + BitVec.ofNat 64 (8*j)) 64 =
      memLoad source.external (src + BitVec.ofNat 64 (8*j)) 64) :
    ∀ i < bytes.size, final.external[dst + BitVec.ofNat 64 i]? = some bytes.data[i]! := by
  intro i hi
  have hsize : bytes.size = 8 * count := hinput.1
  have hj : i / 8 < count := by omega
  have he := memByte_of_memLoad_eq (hread (i / 8) hj) (i % 8) (by omega)
  have hindex : 8 * (i / 8) + i % 8 = i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, hindex] at he
  have hb := hinput.2 ⟨i, hi⟩
  change source.external[BitVec.ofNat 64 (src.toNat + i)]? = some bytes.data[i] at hb
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  obtain ⟨b, hf⟩ := Option.isSome_iff_exists.mp (hallocated i (by omega))
  change (final.external[dst + BitVec.ofNat 64 i]?).getD 0 =
    (source.external[src + BitVec.ofNat 64 i]?).getD 0 at he
  simp only [hf, hb, Option.getD_some] at he
  rw [hf, he, getElem!_pos bytes.data i (by simpa only [ByteArray.size_data] using hi)]

theorem readOutput_of_bytes {routine : Routine} {initial final : RamState} {bytes : ByteArray}
    (hsize : bytes.size < 2^64)
    (hlength : Bytes final.external (initial.regValue routine.outputPointer) 8
      (storedByte (BitVec.ofNat 64 bytes.size)))
    (hbytes : ∀ i < bytes.size,
      final.external[initial.regValue routine.outputPointer + (8 : BitVec 64) + BitVec.ofNat 64 i]? =
        some bytes.data[i]!) :
    readOutput routine initial final = .ok bytes := by
  have hl := readLength_of_bytes hlength
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize] at hl
  have hb : ∀ i < bytes.size,
      readByte final ((initial.regValue routine.outputPointer).toNat + 8 + i) =
        .ok bytes.data[i]! := by
    intro i hi
    simp only [readByte, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have he : final.external[initial.regValue routine.outputPointer + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]? = some bytes.data[i]! := hbytes i hi
    rw [he]
  unfold readOutput
  dsimp only
  rw [hl]
  change (do
    let bs ← (List.range bytes.size).mapM
      (fun i => readByte final ((initial.regValue routine.outputPointer).toNat + 8 + i))
    pure (ByteArray.mk bs.toArray)) = .ok bytes
  rw [readBytes_of_bytes hb]
  change Except.ok (ByteArray.mk bytes.data.toList.toArray) = .ok bytes
  simp only [Array.toArray_toList]

end P256.Proofs.Program
