import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Body

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ReverseWordsAt.of_external {s t : RamState} {base : BitVec 64} {a : Vector (BitVec 64) 4}
    (h : ReverseWordsAt s base a) (hm : t.external = s.external) : ReverseWordsAt t base a := by
  simpa only [ReverseWordsAt, Operand.read, hm] using h

theorem squares_loop [Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {x y : Nat} {a : Vector (BitVec 64) 4}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t)
    (constants : ExponentConstants s t x) (hip : t.RIP = 0x115510)
    (mod0 : t.regValue .r11 = -1) (mod1 : t.regValue .rbx = 0xffffffff)
    (inverse : t.regValue .r12 = -1)
    (hcounter : t.regValue .rax = 0) (hwords : ReverseWordsAt t (exponentFrameBase s) a)
    (hvalue : wordsValue a = y * 2^256 % P256.Spec.Operations.domain.p)
    (count : Nat) (hcount : count ≤ 4) :
    ∃ u fuel b, Advances boundary fuel t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = (if count = 4 then 0x11581c else 0x115510) ∧
      u.regValue .rax = BitVec.ofNat 64 count ∧ u.regValue .r11 = -1 ∧
      u.regValue .rbx = 0xffffffff ∧ u.regValue .r12 = -1 ∧
      ReverseWordsAt u (exponentFrameBase s) b ∧
      wordsValue b = y ^ (2 ^ count) * 2^256 % P256.Spec.Operations.domain.p ∧
      (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read t ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  induction count with
  | zero =>
    exact ⟨t,0,a,(advances_zero _ _ _).mpr rfl,frame,constants,hip,hcounter,mod0,mod1,inverse,
      hwords,by simpa only [Nat.pow_zero,Nat.pow_one] using hvalue,rfl,AgreesExcept.refl _ _⟩
  | succ count ih =>
    have hk : count < 4 := by omega
    obtain ⟨u,fuel,b,ha,hf,hc,hi,hr0,hr11,hr3,hr12,hw,hv,hslot,hag⟩ := ih (by omega)
    have hi' : u.RIP = 0x115510 := by simpa only [show count ≠ 4 by omega,ite_false] using hi
    obtain ⟨v,vf,ha1,hf1,hc1,hi1,h111,h31,h121,hw1,hcounter1,hslot1,hag1⟩ :=
      one_square ctx hf hc hi' hr11 hr3 hr12 hr0 hw
    obtain ⟨w,ha2,hr2,hi2,h02,hag2⟩ := counter ctx hf1 hi1 hk hcounter1
    have hm := hag2.external (by simp [Component.Covers])
    have hag2' : AgreesExcept (components (exponentFrameBase s)) v w := hag2.mono (by simp [components])
    refine ⟨w,fuel+vf+4,squareReducedWords b,(ha.trans ha1).trans ha2,
      frame_of_agrees ctx hf1 hr2 hag2',constants_of_agrees ctx hc1 hag2',?_,h02,?_,?_,?_,
      hw1.of_external hm,?_,?_,((hag.trans hag1).trans hag2').mono (by simp)⟩
    · simpa only [show count+1 = 4 ↔ count = 3 by omega] using hi2
    · exact (hag2.read (r := 11) (n := 64) (by simp)).trans h111
    · exact (hag2.read (r := 3) (n := 64) (by simp)).trans h31
    · exact (hag2.read (r := 12) (n := 64) (by simp)).trans h121
    · rw [squareReducedWords,Correction.words_value]
      rw [squareReduced_montgomery b (y ^ (2 ^ count)) hv,← Nat.pow_add,
        Nat.pow_succ 2 count,Nat.mul_two]
    · have keep : (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read w =
          (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read v := by
        change memLoad w.external _ 64 = memLoad v.external _ 64
        rw [hm]
      exact keep.trans (hslot1.trans hslot)

end P256.Proofs.Sec1.SquareRoot.SquareFour
