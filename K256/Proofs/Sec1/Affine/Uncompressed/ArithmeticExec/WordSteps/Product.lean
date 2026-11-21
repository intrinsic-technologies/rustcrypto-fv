import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Replay
import K256.Proofs.Sec1.Affine.Uncompressed.ProductWords

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

theorem arithmeticProduct_words (s : ArithmeticState) (a b : Limbs)
    (h_slots10 : s.slots 10 = a[0])
    (h_slots6 : s.slots 6 = a[1])
    (h_slots11 : s.slots 11 = a[2])
    (h_slots7 : s.slots 7 = a[3])
    (h_slots4 : s.slots 4 = a[4])
    (h_slots3 : s.slots 3 = b[0])
    (h_slots2 : s.slots 2 = b[1])
    (h_slots9 : s.slots 9 = b[2])
    (h_slots5 : s.slots 5 = b[3])
    (h_slots0 : s.slots 0 = b[4])
    (h_regs0 : s.regs 0 = b[0])
    (h_regs5 : s.regs 5 = b[1])
    (h_regs15 : s.regs 15 = b[2])
    (h_regs1 : s.regs 1 = b[3])
    (h_regs12 : s.regs 12 = b[4])
    (h_regs9 : s.regs 9 = 0xfffffffffffff)
    (h_regs13 : s.regs 13 = a[2])
    (h_regs14 : s.regs 14 = 0x1000003d10) :
    (arithmeticProduct s).productWords = cubeProduct a b := by
  let s0 : ArithmeticState :=
    { regs := fun
        | 0 => b[0]
        | 1 => b[3]
        | 5 => b[1]
        | 9 => 0xfffffffffffff
        | 12 => b[4]
        | 13 => a[2]
        | 14 => 0x1000003d10
        | 15 => b[2]
        | i => s.regs i,
      slots := fun
        | 0 => b[4]
        | 2 => b[1]
        | 3 => b[0]
        | 4 => a[4]
        | 5 => b[3]
        | 6 => a[1]
        | 7 => a[3]
        | 9 => b[2]
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
  word_checkpoint s1 step0 := arithmeticStep18Last s0
  word_checkpoint s2 step1 := arithmeticStep19 s1
  word_checkpoint s3 step2 := arithmeticStep20 s2
  word_checkpoint s4 step3 := arithmeticStep21 s3
  word_checkpoint s5 step4 := arithmeticStep22 s4
  word_checkpoint s6 step5 := arithmeticStep23 s5
  word_checkpoint s7 step6 := arithmeticStep24 s6
  word_checkpoint s8 step7 := arithmeticStep25 s7
  word_checkpoint s9 step8 := arithmeticStep26 s8
  word_checkpoint s10 step9 := arithmeticStep27 s9
  word_checkpoint s11 step10 := arithmeticStep28 s10
  word_checkpoint s12 step11 := arithmeticStep29First s11
  word_checkpoint k0 kernel0 := cubeProduct11FE67H a b
  word_checkpoint k1 kernel1 := cubeProduct11FED2 a b k0
  word_checkpoint k2 kernel2 := cubeProduct11FF5F a b k1
  word_checkpoint k3 kernel3 := cubeProduct11FFD9C a b k2
  word_checkpoint k4 kernel4 := cubeProduct120038 a b k3
  word_checkpoint k5 kernel5 := cubeProduct1200C8 a b k4
  word_checkpoint k6 kernel6 := cubeProduct12014D k5
  word_checkpoint k7 kernel7 := cubeProduct1201AB k6
  rw [arithmeticProduct, hbase, step0, step1, step2, step3, step4, step5, step6, step7, step8, step9,
    step10, step11, cubeProduct, kernel0, kernel1, kernel2, kernel3, kernel4, kernel5, kernel6,
    kernel7]
  rfl

end K256.Proofs.Sec1.Affine.Uncompressed
