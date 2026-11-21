import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Replay
import K256.Proofs.Sec1.Affine.Uncompressed.SquareWords

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

theorem arithmeticSquareX_words (s : ArithmeticState) (a : Limbs)
    (h_slots10 : s.slots 10 = a[0])
    (h_slots6 : s.slots 6 = a[1])
    (h_slots11 : s.slots 11 = a[2])
    (h_slots7 : s.slots 7 = a[3])
    (h_slots4 : s.slots 4 = a[4])
    (h_regs11 : s.regs 11 = 0x1000003d10) :
    (arithmeticSquareX s).squareXWords = squareX a := by
  let s0 : ArithmeticState :=
    { regs := fun
        | 11 => 0x1000003d10
        | i => s.regs i,
      slots := fun
        | 4 => a[4]
        | 6 => a[1]
        | 7 => a[3]
        | 10 => a[0]
        | 11 => a[2]
        | i => s.slots i }
  have hbase : s = s0 := by
    cases s with | mk regs slots =>
      change ArithmeticState.mk regs slots = ArithmeticState.mk _ _
      congr 1
      · funext i
        try dsimp only [s0]
        split <;> first | assumption | rfl
      · funext i
        try dsimp only [s0]
        split <;> first | assumption | rfl
  word_checkpoint s1 step0 := arithmeticStep9Last s0
  word_checkpoint s2 step1 := arithmeticStep10 s1
  word_checkpoint s3 step2 := arithmeticStep11 s2
  word_checkpoint s4 step3 := arithmeticStep12 s3
  word_checkpoint s5 step4 := arithmeticStep13 s4
  word_checkpoint s6 step5 := arithmeticStep14 s5
  word_checkpoint s7 step6 := arithmeticStep15 s6
  word_checkpoint s8 step7 := arithmeticStep16 s7
  word_checkpoint s9 step8 := arithmeticStep17 s8
  word_checkpoint s10 step9 := arithmeticStep18First s9
  word_checkpoint k0 kernel0 := squareX11FBD1H a
  word_checkpoint k1 kernel1 := squareX11FC4F a k0
  word_checkpoint k2 kernel2 := squareX11FCAB a k1
  word_checkpoint k3 kernel3 := squareX11FD1DH a k2
  word_checkpoint k4 kernel4 := squareX11FD89 a k3
  word_checkpoint k5 kernel5 := squareX11FDF2 k4
  rw [arithmeticSquareX, hbase, step0, step1, step2, step3, step4, step5, step6, step7, step8, step9,
    squareX, kernel0, kernel1, kernel2, kernel3, kernel4, kernel5]
  rfl

end K256.Proofs.Sec1.Affine.Uncompressed
