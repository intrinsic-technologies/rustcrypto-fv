import AesGcm.Proofs.Machine.GHASH.Karatsuba
import AesGcm.Proofs.Machine.GHASH.KeyAdjustment

namespace AesGcm.Proofs.Machine.GHASH

def polyvalMultiplyWords (x0 x1 y0 y1 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p := wideMul64 x0 y0
  let q := wideMul64 x1 y1
  let t := wideMul64 (x0 ^^^ x1) (y0 ^^^ y1)
  polyvalReduceWords (p.setWidth 64)
    (t.setWidth 64 ^^^ p.setWidth 64 ^^^ q.setWidth 64 ^^^ high64 p)
    (q.setWidth 64 ^^^ high64 p ^^^ high64 q ^^^ high64 t) (high64 q)

theorem joinWords_low128 (w0 w1 w2 w3 : BitVec 64) :
    (joinWords w0 w1 w2 w3).setWidth 128 = w1 ++ w0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [joinWords, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  grind

theorem polyvalMultiplyWords_eq_gcmReduce (x0 x1 y0 y1 : BitVec 64) :
    let r := polyvalMultiplyWords x0 x1 y0 y1
    (r.2 ++ r.1).reverse = gcmReduce (wideMul128 (x1 ++ x0) (y1 ++ y0)) := by
  rw [wideMul128_words]
  change _ = ((polyvalSteps 128 (joinWords _ _ _ _)).setWidth 128).reverse
  rw [polyvalSteps_128_words, joinWords_low128]
  rfl

theorem polyvalMultiplyWords_eq_standard (x0 x1 y0 y1 : BitVec 64) (h : BitVec 128)
    (hy : y1 ++ y0 = polyvalMulX h) :
    let r := polyvalMultiplyWords x0 x1 y0 y1
    toGcmBits (r.2 ++ r.1).reverse =
      Standards.NIST.GCM.mul (toGcmBits (x1 ++ x0).reverse) (toGcmBits h.reverse) := by
  dsimp only
  rw [polyvalMultiplyWords_eq_gcmReduce, hy, gcmReduce_wideMul128_eq_standard]

theorem polyvalMultiplyWords_adjusted_eq_standard (x0 x1 h0 h1 : BitVec 64) :
    let k := polyvalKeyWords h0 h1
    let r := polyvalMultiplyWords x0 x1 k.1 k.2
    toGcmBits (r.2 ++ r.1).reverse =
      Standards.NIST.GCM.mul (toGcmBits (x1 ++ x0).reverse) (toGcmBits (h1 ++ h0).reverse) := by
  exact polyvalMultiplyWords_eq_standard x0 x1 _ _ _ (polyvalKeyWords_eq_mulX h0 h1)


end AesGcm.Proofs.Machine.GHASH
