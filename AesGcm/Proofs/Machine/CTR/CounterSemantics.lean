import AesGcm.Proofs.Machine.CTR.CounterBlocks
import AesGcm.Proofs.Machine.CTR.CounterBytes
import AesGcm.Proofs.Machine.CTR.CounterModel
import AesGcm.Proofs.Machine.Fixslice.Operations

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86Proofs Standards.NIST.GCM

theorem counterBlock_bits (mem : Ram) (counter : BitVec 64) (j : Fin 4) :
    bitsOfBytes (Fixslice.toStandard (counterBlocks mem counter) j) =
      (Vector.ofFn fun i : Fin 96 ↦
        (storedByte (memLoad mem (counter + BitVec.ofNat 64 (4 * (i.val / 32))) 32)
          (i.val / 8 % 4)).toNat.testBit (7 - i.val % 8)) ++
      Vector.ofFn (fun i : Fin 32 ↦
        (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32 +
          BitVec.ofNat 32 j.val).getMsbD i.val) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < 96
  · simp only [bitsOfBytes, Fixslice.toStandard, counterBlocks, Vector.getElem_ofFn,
      UInt8.ofBitVec_toBitVec, counterWord, Vector.getElem_append_left h]
    simp only [show i / 8 / 4 < 3 by omega, ite_eq_left]
    rw [show i / 8 / 4 = i / 32 by omega]
  · have hword := congrArg (fun v : Vector Bool 32 ↦ v[i - 96]'(by omega))
      (bitsOfBytes_bswap32 (memLoad mem (counter + 12) 32 +
        memLoad mem (counter + 16) 32 + BitVec.ofNat 32 j.val))
    simp only [bitsOfBytes, Fixslice.toStandard, counterBlocks, Vector.getElem_ofFn,
      UInt8.ofBitVec_toBitVec, counterWord,
      Vector.getElem_append_right (n := 96) (m := 32) (by omega) (by omega : 96 ≤ i)]
    simp only [show ¬ i / 8 / 4 < 3 by omega, ↓reduceIte]
    simpa only [bitsOfBytes, Vector.getElem_ofFn,
      show (i - 96) / 8 = i / 8 % 4 by omega,
      show (i - 96) % 8 = i % 8 by omega] using hword

theorem counterBlocks_eq_repeat_inc (mem : Ram) (counter : BitVec 64) (j : Fin 4) :
    bitsOfBytes (Fixslice.toStandard (counterBlocks mem counter) j) =
      Nat.repeat (inc 32) j.val
        (bitsOfBytes (Fixslice.toStandard (counterBlocks mem counter) 0)) := by
  rw [counterBlock_bits, counterBlock_bits, repeat_inc_append_word]
  simp [Fin.val_zero]

end AesGcm.Proofs.Machine.CTR
