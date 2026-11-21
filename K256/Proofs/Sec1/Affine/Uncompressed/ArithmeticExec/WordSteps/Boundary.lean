import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Views
import K256.Proofs.Sec1.Affine.Uncompressed.Equation
import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

theorem arithmeticEquation_word (s : ArithmeticState) (hm : s.regs 3 = 0xfffffffffffff) :
    (arithmeticEquation s).regs 7 = BitVec.ofNat 64 (equation s.productWords s.squareYWords).toNat := by
  let c := s.productWords
  let y := s.squareYWords
  let top := (0x3fffffffffffc : Word) + (c[4] - y[4])
  let t0 := (0x3ffffbfffff0c3 : Word) + (c[0] - y[0]) + 0x1000003d1 * (top >>> 48)
  let t1 := (c[1] - y[1]) + 0x3ffffffffffffc + (t0 >>> 52)
  let t2 := (c[2] - y[2]) + 0x3ffffffffffffc + (t1 >>> 52)
  let t3 := (c[3] - y[3]) + 0x3ffffffffffffc + (t2 >>> 52)
  let t4 := (t3 >>> 52) + (top &&& 0xffffffffffff)
  change BitVec.ofNat 64 (((t0 ^^^ 0x1000003d0) &&& t1 &&& t2 &&& t3 &&& (0xf000000000000 ^^^ t4)) == s.regs 3).toNat =
    BitVec.ofNat 64 (equation c y).toNat
  simp only [hm, t4, t3, t2, t1, t0, top, equation]
  ac_rfl

theorem arithmeticPrepare_regs (s : ArithmeticState) (a b c d : Word) (ok : Bool)
    (h0 : (s.regs 0).setWidth 8 = BitVec.ofNat 8 ok.toNat)
    (h15 : s.regs 15 = d &&& 0xfffffffffffff)
    (h13 : s.regs 13 = shldResult 12 c d &&& 0xfffffffffffff)
    (h12 : s.regs 12 = shldResult 24 b c) (h3 : s.regs 3 = shldResult 36 a b)
    (h14 : s.regs 14 = a >>> 16) (h5 : s.regs 5 = 0xfffffffffffff) :
    (arithmeticPrepare s).yRegs = (if ok then unpack a b c d else Vector.replicate 5 0) ∧
    (arithmeticPrepare s).slots 24 = BitVec.ofNat 64 ok.toNat := by
  have rightOnes (x : Word) : x &&& 0xffffffffffffffff#64 = x := BitVec.and_allOnes
  have leftOnes (x : Word) : 0xffffffffffffffff#64 &&& x = x := BitVec.allOnes_and
  cases ok <;>
    simp only [arithmeticPrepare, arithmeticStep0First, ArithmeticState.yRegs, h0,
      h15, h13, h12, h3, h14, h5, unpack, Bool.toNat, Bool.cond_false, Bool.cond_true, Bool.false_eq_true,
      ↓reduceIte, BitVec.reduceSetWidth, BitVec.reduceNeg, BitVec.and_zero,
      BitVec.zero_and, rightOnes, leftOnes, and_true, BitVec.and_comm (0xfffffffffffff : Word) _]
    <;> rfl

end K256.Proofs.Sec1.Affine.Uncompressed
