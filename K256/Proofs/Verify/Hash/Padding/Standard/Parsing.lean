import K256.Proofs.Verify.Hash.Blocks
import Standards.SECG.ECC.Encoding

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

theorem parse_getElem_eq_blockWords (bits : Array Bool) (i : Nat)
    (hi : i < bits.size / 512) :
    (Standards.NIST.SHA2.SHA256.parse bits)[i]'(by
      simpa only [Standards.NIST.SHA2.SHA256.parse, Array.size_ofFn] using hi) =
      Vector.ofFn (fun j : Fin 16 => BitVec.ofNat 32
        (Reference.bitsToNat
          ((bits.extract (512 * i) (512 * (i + 1))).extract
            (32 * j.val) (32 * (j.val + 1))))) := by
  simp only [Standards.NIST.SHA2.SHA256.parse, Array.getElem_ofFn]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  let wordBits : Vector Bool 32 := Vector.ofFn fun n : Fin 32 =>
    bits[512 * i + 32 * j + n.val]'(by have hn := n.isLt; omega)
  change Standards.NIST.SHA2.bitsToWord wordBits = BitVec.ofNat 32
    (Reference.bitsToNat
      ((bits.extract (512 * i) (512 * (i + 1))).extract
        (32 * j) (32 * (j + 1))))
  have hblock : (bits.extract (512 * i) (512 * (i + 1))).size = 512 := by
    simp only [Array.size_extract]
    omega
  have hword : ((bits.extract (512 * i) (512 * (i + 1))).extract
      (32 * j) (32 * (j + 1))).size = 32 := by
    simp only [Array.size_extract, hblock]
    omega
  have hslice : wordBits.toArray =
      (bits.extract (512 * i) (512 * (i + 1))).extract
        (32 * j) (32 * (j + 1)) := by
    apply Array.ext
    · simp only [wordBits, Vector.toArray_ofFn, Array.size_ofFn, hword]
    · intro n hn hs
      simp only [wordBits, Vector.toArray_ofFn, Array.getElem_ofFn, Array.getElem_extract]
      congr 1
      omega
  apply (BitVec.toNat_eq_nat.mp ?_).2
  simp only [Standards.NIST.SHA2.bitsToWord, BitVec.toNat_cast,
    Reference.bitsToNat, ← Vector.toList_toArray]
  rw [hslice]

end K256.Proofs.Verify.Hash
