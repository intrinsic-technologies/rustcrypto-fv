import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Replay
import K256.Proofs.Sec1.Affine.Uncompressed.SquareWords

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

theorem arithmeticSquareY_words (s : ArithmeticState) (a : Limbs)
    (h_regs15 : s.regs 15 = a[0])
    (h_regs13 : s.regs 13 = a[1])
    (h_regs12 : s.regs 12 = a[2])
    (h_regs5 : s.regs 5 = a[3])
    (h_regs14 : s.regs 14 = a[4])
    (h_regs0 : s.regs 0 = a[3]) :
    (arithmeticSquareY s).squareYWords = squareY a := by
  let s0 : ArithmeticState :=
    { regs := fun
        | 0 => a[3]
        | 5 => a[3]
        | 12 => a[2]
        | 13 => a[1]
        | 14 => a[4]
        | 15 => a[0]
        | i => s.regs i,
      slots := s.slots }
  have hbase : s = s0 := by
    cases s with | mk regs slots =>
      change ArithmeticState.mk regs slots = ArithmeticState.mk _ _
      congr 1
      · funext i
        try dsimp only [s0]
        split <;> first | assumption | rfl
  word_checkpoint s1 step0 := arithmeticStep0Last s0
  word_checkpoint s2 step1 := arithmeticStep1 s1
  word_checkpoint s3 step2 := arithmeticStep2 s2
  word_checkpoint s4 step3 := arithmeticStep3 s3
  word_checkpoint s5 step4 := arithmeticStep4 s4
  word_checkpoint s6 step5 := arithmeticStep5 s5
  word_checkpoint s7 step6 := arithmeticStep6 s6
  word_checkpoint s8 step7 := arithmeticStep7 s7
  word_checkpoint s9 step8 := arithmeticStep8 s8
  word_checkpoint s10 step9 := arithmeticStep9First s9
  word_checkpoint k0 kernel0 := squareY11F919H a
  word_checkpoint k1 kernel1 := squareY11F998 a k0
  word_checkpoint k2 kernel2 := squareY11F9FEH a k1
  word_checkpoint k3 kernel3 := squareY11FA79 a k2
  word_checkpoint k4 kernel4 := squareY11FAED a k3
  word_checkpoint k5 kernel5 := squareY11FB56 k4
  rw [arithmeticSquareY, hbase, step0, step1, step2, step3, step4, step5, step6, step7, step8, step9,
    squareY, kernel0, kernel1, kernel2, kernel3, kernel4, kernel5]
  rfl

end K256.Proofs.Sec1.Affine.Uncompressed
