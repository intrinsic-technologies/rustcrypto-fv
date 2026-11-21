import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Boundary
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Product
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.SquareX
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.SquareY

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

private theorem productAfterSquareX (s : ArithmeticState) :
    (arithmeticProduct (arithmeticSquareX s)).productWords =
      cubeProduct s.xWords (arithmeticSquareX s).squareXWords := by
  exact arithmeticProduct_words _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl

private theorem squareXAfterSquareY (s : ArithmeticState) :
    (arithmeticSquareX (arithmeticSquareY s)).squareXWords = squareX (arithmeticSquareY s).xWords :=
  arithmeticSquareX_words _ _ rfl rfl rfl rfl rfl rfl

private theorem squareYAfterPrepare (s : ArithmeticState) :
    (arithmeticSquareY (arithmeticPrepare s)).squareYWords = squareY (arithmeticPrepare s).yRegs :=
  arithmeticSquareY_words _ _ rfl rfl rfl rfl rfl rfl

private theorem equationAfterProduct (s : ArithmeticState) :
    (arithmeticEquation (arithmeticProduct s)).regs 7 =
      BitVec.ofNat 64 (equation (arithmeticProduct s).productWords (arithmeticProduct s).squareYWords).toNat :=
  arithmeticEquation_word _ rfl

private theorem savedCoordinates (s : ArithmeticState) :
    (arithmeticRun s).xWords = s.xWords ∧ (arithmeticRun s).yWords = (arithmeticPrepare s).yRegs ∧
      (arithmeticRun s).slots 24 = (arithmeticPrepare s).slots 24 := ⟨rfl, rfl, rfl⟩

private theorem productSquareYWords (s : ArithmeticState) :
    (arithmeticProduct (arithmeticSquareX s)).squareYWords = s.squareYWords := rfl

private theorem squareYXWords (s : ArithmeticState) :
    (arithmeticSquareY (arithmeticPrepare s)).xWords = s.xWords := rfl

theorem arithmeticRun_words (s : ArithmeticState) (a b c d : Word) (ok : Bool)
    (h0 : (s.regs 0).setWidth 8 = BitVec.ofNat 8 ok.toNat)
    (h15 : s.regs 15 = d &&& 0xfffffffffffff)
    (h13 : s.regs 13 = shldResult 12 c d &&& 0xfffffffffffff)
    (h12 : s.regs 12 = shldResult 24 b c) (h3 : s.regs 3 = shldResult 36 a b)
    (h14 : s.regs 14 = a >>> 16) (h5 : s.regs 5 = 0xfffffffffffff) :
    let y := if ok then unpack a b c d else Vector.replicate 5 0
    (arithmeticRun s).regs 7 =
        BitVec.ofNat 64 (equation (cubeProduct s.xWords (squareX s.xWords)) (squareY y)).toNat ∧
      (arithmeticRun s).xWords = s.xWords ∧ (arithmeticRun s).yWords = y ∧
      (arithmeticRun s).slots 24 = BitVec.ofNat 64 ok.toNat := by
  obtain ⟨hy, hflag⟩ := arithmeticPrepare_regs s a b c d ok h0 h15 h13 h12 h3 h14 h5
  obtain ⟨hx, hys, hfs⟩ := savedCoordinates s
  refine ⟨?_, hx, hys.trans hy, hfs.trans hflag⟩
  simp only [arithmeticRun_phases, equationAfterProduct, productAfterSquareX, squareXAfterSquareY,
    productSquareYWords, squareYAfterPrepare, squareYXWords, hy]

end K256.Proofs.Sec1.Affine.Uncompressed
