import AesGcm.Proofs.Machine.GHASH.WordMultiplication

namespace AesGcm.Proofs.Machine.GHASH

def toBigEndianBytes (x : BitVec 128) : Vector UInt8 16 :=
  Vector.ofFn (fun i => ⟨x.extractLsb' (8 * (15 - i.val)) 8⟩)

theorem toGcmBits_reverse_eq_bitsOfBytes (x : BitVec 128) :
    toGcmBits x.reverse = Standards.NIST.GCM.bitsOfBytes (toBigEndianBytes x) := by
  apply Vector.ext
  intro i hi
  simp only [toGcmBits, Standards.NIST.GCM.bitsOfBytes, toBigEndianBytes,
    Vector.getElem_ofFn, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  change (decide (i < 128) && x.getLsbD (128 - 1 - i)) =
    (x.extractLsb' (8 * (15 - i / 8)) 8).getLsbD (7 - i % 8)
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 7 - i % 8 < 8 from by omega]
  congr 1
  omega

theorem polyvalMultiplyWords_adjusted_bytes (x0 x1 h0 h1 : BitVec 64) :
    let k := polyvalKeyWords h0 h1
    let r := polyvalMultiplyWords x0 x1 k.1 k.2
    Standards.NIST.GCM.bitsOfBytes (toBigEndianBytes (r.2 ++ r.1)) =
      Standards.NIST.GCM.mul
        (Standards.NIST.GCM.bitsOfBytes (toBigEndianBytes (x1 ++ x0)))
        (Standards.NIST.GCM.bitsOfBytes (toBigEndianBytes (h1 ++ h0))) := by
  simpa only [toGcmBits_reverse_eq_bitsOfBytes] using
    polyvalMultiplyWords_adjusted_eq_standard x0 x1 h0 h1

end AesGcm.Proofs.Machine.GHASH
