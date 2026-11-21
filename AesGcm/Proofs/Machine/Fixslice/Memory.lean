import AesGcm.Proofs.Machine.Fixslice.Conversion
import X86Proofs.Program.ReadWrite.Store

namespace AesGcm.Proofs.Machine.Fixslice

open X86 X86.Machine X86Proofs

def memoryBlock (m : Ram) (a : BitVec 64) : Fin 16 → BitVec 8 :=
  fun j ↦ (memByte m (a + BitVec.ofNat 64 j.val)).toBitVec

def memoryBlocks (m : Ram) (a : BitVec 64) : Blocks :=
  fun b ↦ memoryBlock m (a + BitVec.ofNat 64 (16 * b.val))

theorem storedByte_toBitVec {n : Nat} (v : BitVec n) (i : Nat) :
    (storedByte v i).toBitVec = (v >>> (8 * i)).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [storedByte]

theorem readReordered_memLoad (m : Ram) (a : BitVec 64) (h : Fin 2) :
    readReordered (memoryBlock m a) h =
      packBytes (fun q ↦
        ((memLoad m (a + BitVec.ofNat 64 (4 * h.val + 8 * (q.val % 2))) 32) >>>
          (8 * (q.val / 2))).setWidth 8) := by
  unfold readReordered
  congr 1
  funext q
  rw [← storedByte_toBitVec, storedByte_memLoad _ _ _ (by omega)]
  simp only [memoryBlock, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem inputPacking_memLoad (m : Ram) (a : BitVec 64) (p : Fin 8) :
    inputPacking (memoryBlocks m a) p =
      packBytes (fun q ↦
        ((memLoad m (a + BitVec.ofNat 64
          (16 * (p.val % 4) + 4 * (p.val / 4) + 8 * (q.val % 2))) 32) >>>
            (8 * (q.val / 2))).setWidth 8) := by
  simp only [inputPacking, memoryBlocks, readReordered_memLoad]
  congr 1
  funext q
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]

theorem writeReordered_storedByte (x : BitVec 64) (r : Fin 4) (h : Fin 2) :
    writeReordered x r h = (storedByte x (2 * r.val + h.val)).toBitVec := by
  rw [storedByte_toBitVec]
  simp only [writeReordered]
  congr 2
  omega

theorem writeReordered_memLoad (m : Ram) (a : BitVec 64) (r : Fin 4) (h : Fin 2) :
    writeReordered (memLoad m a 64) r h =
      (memByte m (a + BitVec.ofNat 64 (2 * r.val + h.val))).toBitVec := by
  rw [writeReordered_storedByte, storedByte_memLoad _ _ _ (by omega)]

theorem memLoad_writeReordered (m : Ram) (a : BitVec 64) (x : BitVec 64)
    (r : Fin 4) (h : Fin 2) :
    memLoad (memStore m a (writeReordered x r h)) a 8 =
      (storedByte x (2 * r.val + h.val)).toBitVec := by
  rw [memLoad_memStore_8, writeReordered_storedByte]

end AesGcm.Proofs.Machine.Fixslice
