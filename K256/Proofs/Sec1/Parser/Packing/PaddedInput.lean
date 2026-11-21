import K256.Proofs.Sec1.Parser.Packing.Rearrange
import K256.Proofs.Common.Lift.Rep

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem affineInput {sp src : BitVec 64} {m : Ram} {bytes : ByteArray}
    (size : bytes.size ≤ 65)
    (input : ∀ i (hi : i < bytes.size), memByte m (src + BitVec.ofNat 64 i) = bytes[i])
    (tail : ∀ i, bytes.size ≤ i → i < 65 → memByte m (sp + 160 + BitVec.ofNat 64 i) = 0) :
    ∀ i < 65,
      memByte (affineMemory sp (memCopy m (sp + 160) src bytes.size))
        (sp + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0 := by
  intro i hi
  rw [affineMemory_bytes sp _ i hi]
  by_cases hb : i < bytes.size
  · have hbound : i < (8 * bytes.size) / 8 := by omega
    have copied := memStore_getElem?_self_of_le m (sp + 160)
      (memLoad m src (8 * bytes.size)) (by omega) i hbound
    change ((memStore m (sp + 160) _)[sp + 160 + BitVec.ofNat 64 i]?).getD 0 = _
    rw [copied, Option.getD_some, storedByte_memLoad _ _ _ hbound, input i hb,
      getElem?_pos bytes.data i hb]
    rfl
  · have keep := memStore_getElem?_of_ne m (sp + 160) (memLoad m src (8 * bytes.size))
      (sp + 160 + BitVec.ofNat 64 i) (by
        intro j hj h
        have := add_ofNat_inj (sp + 160) (i := i) (j := j) (by omega) (by omega) h
        omega)
    change ((memStore m (sp + 160) _)[sp + 160 + BitVec.ofNat 64 i]?).getD 0 = _
    rw [keep, getElem?_neg bytes.data i hb]
    exact tail i (by omega) hi

theorem affineInput_words {sp src : BitVec 64} {m : Ram} {bytes : ByteArray}
    (size : bytes.size ≤ 65)
    (input : ∀ i (hi : i < bytes.size), memByte m (src + BitVec.ofNat 64 i) = bytes[i])
    (tail : ∀ i, bytes.size ≤ i → i < 65 → memByte m (sp + 160 + BitVec.ofNat 64 i) = 0) :
    WordsAt (affineMemory sp (memCopy m (sp + 160) src bytes.size)) (sp + 4) 8
      (Vector.ofFn fun i : Fin 65 => (bytes.data[i.val]?.getD 0).toBitVec) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  apply memLoad_eq_of_memByte (by decide)
  intro j hj
  obtain rfl : j = 0 := by omega
  simp only [wordAddr, Nat.reduceDiv, Nat.one_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  exact (affineInput size input tail i hi).trans (by simp [storedByte])

end K256.Proofs.Sec1.Parser.Packing
