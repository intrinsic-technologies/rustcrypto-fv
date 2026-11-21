import AesGcm.Spec.GCM
import X86Proofs.Step.Memory
import X86Proofs.Instructions.Bswap.Operation

namespace AesGcm.Proofs.Machine.CTR
open X86Proofs

theorem bitsOfBytes_bswap32 (word : BitVec 32) :
    Standards.NIST.GCM.bitsOfBytes
      (Vector.ofFn fun i : Fin 4 ↦ storedByte (bswapSpec word) i.val) =
      Vector.ofFn (fun i : Fin 32 ↦ word.getMsbD i.val) := by
  apply Vector.ext
  intro i hi
  simp only [Standards.NIST.GCM.bitsOfBytes, Vector.getElem_ofFn, storedByte,
    UInt8.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  change (decide (7 - i % 8 < 8) && (bswapSpec word).getLsbD (8 * (i / 8) + (7 - i % 8))) = _
  rw [bswapSpec, getLsbD_ofLanes _ _ (by omega)]
  simp only [lane, BitVec.getLsbD_extractLsb', Nat.reduceDiv, Nat.reduceMul,
    BitVec.getMsbD_eq_getLsbD, hi, decide_true, Bool.true_and]
  have hd : (8 * (i / 8) + (7 - i % 8)) / 8 = i / 8 := by omega
  have hm : (8 * (i / 8) + (7 - i % 8)) % 8 = 7 - i % 8 := by omega
  simp only [hd, hm, show 7 - i % 8 < 8 by omega, decide_true, Bool.true_and]
  rw [ite_eq_left (by omega)]
  congr 1
  omega

end AesGcm.Proofs.Machine.CTR
