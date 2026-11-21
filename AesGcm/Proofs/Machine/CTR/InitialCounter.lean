import AesGcm.Proofs.Machine.CTR.CounterBlocks
import AesGcm.Proofs.Machine.CTR.CounterSemantics
import AesGcm.Proofs.Machine.Tag.Semantics
import AesGcm.Proofs.Machine.Runtime.Preservation
namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86Proofs X86Proofs.Refine Standards.NIST.GCM
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1200000 in
theorem initialCounterBlock_nonce96 (original mem : Ram) (noncePtr counter : BitVec 64)
    (cipher : Vector Bool 128 → Vector Bool 128) (nonce : Vector UInt8 12)
    (hnonce : (span noncePtr 12).HasBytes original ⟨nonce.toArray⟩)
    (words : ∀ k : Fin 3, memLoad mem (counter + BitVec.ofNat 64 (4 * k.val)) 32 =
      memLoad original (noncePtr + BitVec.ofNat 64 (4 * k.val)) 32)
    (w3 : memLoad mem (counter + 12) 32 = 1)
    (w4 : memLoad mem (counter + 16) 32 = 1) :
    bitsOfBytes (initialCounterBlock mem counter) =
      inc 32 (preCounterBlock cipher (bitsOfBytes nonce)) := by
  have he : initialCounterBlock mem counter = Fixslice.toStandard (counterBlocks mem counter) 0 := by
    apply Vector.ext
    intro i hi
    simp only [initialCounterBlock, Fixslice.toStandard, counterBlocks, Vector.getElem_ofFn,
      UInt8.ofBitVec_toBitVec]
  rw [he, counterBlock_bits, w3, w4, Tag.preCounterBlock_nonce96]
  have hone : zeros 31 ++ #v[true] =
      Vector.ofFn (fun i : Fin 32 ↦ (1#32).getMsbD i.val) := by decide +kernel
  rw [Vector.append_assoc, hone]
  simp only [Vector.cast_rfl, Fin.val_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  rw [inc_append_word]
  apply congrArg (fun head : Vector Bool 96 ↦ head ++ Vector.ofFn (fun i : Fin 32 ↦ (2#32).getMsbD i.val))
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, bitsOfBytes]
  have hw := congrArg (fun w : BitVec 32 ↦ storedByte w (i / 8 % 4))
    (words ⟨i / 32, by omega⟩)
  conv at hw =>
    rhs
    rw [storedByte_memLoad _ _ _ (by omega)]
  have hb := hnonce.2 ⟨i / 8, by simpa only [ByteArray.size, Vector.size_toArray] using (show i / 8 < 12 by omega)⟩
  change original[BitVec.ofNat 64 (noncePtr.toNat + i / 8)]? = some nonce[i / 8] at hb
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  have haddr : 4 * (i / 32) + i / 8 % 4 = i / 8 := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, haddr, memByte, PhysicalMemory.read,
    hb, Option.getD_some] at hw
  rw [hw]
theorem initialCounterBlock_eq_standard (mem : Ram) (counter : BitVec 64) :
    initialCounterBlock mem counter = Fixslice.toStandard (counterBlocks mem counter) 0 := by
  apply Vector.ext
  intro i hi
  simp only [initialCounterBlock, Fixslice.toStandard, counterBlocks, Vector.getElem_ofFn,
    UInt8.ofBitVec_toBitVec]

theorem initialCounterBlock_advance (before after : Ram) (counter : BitVec 64) (n : Nat)
    (words : ∀ k : Fin 3, memLoad after (counter + BitVec.ofNat 64 (4 * k.val)) 32 =
      memLoad before (counter + BitVec.ofNat 64 (4 * k.val)) 32)
    (w3 : memLoad after (counter + 12) 32 = memLoad before (counter + 12) 32)
    (w4 : memLoad after (counter + 16) 32 =
      memLoad before (counter + 16) 32 + BitVec.ofNat 32 n) :
    bitsOfBytes (initialCounterBlock after counter) =
      Nat.repeat (inc 32) n (bitsOfBytes (initialCounterBlock before counter)) := by
  rw [initialCounterBlock_eq_standard, initialCounterBlock_eq_standard,
    counterBlock_bits, counterBlock_bits, repeat_inc_append_word, w3, w4]
  simp only [Fin.val_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc]
  apply congrArg (fun head : Vector Bool 96 ↦ head ++ Vector.ofFn (fun i : Fin 32 ↦
    (memLoad before (counter + 12) 32 +
      (memLoad before (counter + 16) 32 + BitVec.ofNat 32 n)).getMsbD i.val))
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rw [words ⟨i / 32, by omega⟩]

theorem initialCounterBlock_of_frame {before after : Ram} {regions : List MemoryRegion}
    {counter : BitVec 64} (hf : RamWriteFrame before after regions)
    (ho : Outside regions counter 20) :
    initialCounterBlock after counter = initialCounterBlock before counter := by
  have loads (n : Nat) (hn : n + 4 ≤ 20) :
      memLoad after (counter + BitVec.ofNat 64 n) 32 =
      memLoad before (counter + BitVec.ofNat 64 n) 32 :=
    hf.memLoad_eq (outside_subregion ho (by omega) (by omega))
  apply Vector.ext
  intro i hi
  simp only [initialCounterBlock, Vector.getElem_ofFn, counterWord]
  split
  · rw [loads _ (by omega)]
  · have h12 : memLoad after (counter + 12) 32 = memLoad before (counter + 12) 32 := loads 12 (by decide)
    have h16 : memLoad after (counter + 16) 32 = memLoad before (counter + 16) 32 := loads 16 (by decide)
    rw [h12, h16]

end AesGcm.Proofs.Machine.CTR
