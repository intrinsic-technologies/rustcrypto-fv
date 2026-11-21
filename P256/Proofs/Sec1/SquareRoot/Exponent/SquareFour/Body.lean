import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Prepare
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Round
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def squareReducedWords (a : Vector (BitVec 64) 4) : Vector (BitVec 64) 4 :=
  Correction.words (squareReduced a)

theorem one_square [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x k : Nat} {a : Vector (BitVec 64) 4}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t)
    (constants : ExponentConstants s t x) (rip : t.RIP = 0x115510)
    (mod0 : t.regValue .r11 = -1) (mod1 : t.regValue .rbx = 0xffffffff)
    (inverse : t.regValue .r12 = -1)
    (counter : t.regValue .rax = BitVec.ofNat 64 k)
    (words : ReverseWordsAt t (exponentFrameBase s) a) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = 0x11580d ∧ u.regValue .r11 = -1 ∧ u.regValue .rbx = 0xffffffff ∧
      u.regValue .r12 = -1 ∧ ReverseWordsAt u (exponentFrameBase s) (squareReducedWords a) ∧
      (Operand.mem (exponentFrameBase s + 0x7c) : Operand 32).read u = BitVec.ofNat 32 k ∧
      (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read t ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨p,rp,fp,cp,ip,acc,p13,p14,p11,p3,p12,digits,rev,count,slot,ap⟩ :=
    prepare_square ctx frame constants rip counter words
  have state : RoundState s p x a ⟨0,0,⟨0,0,0,0,false⟩⟩ 0 :=
    ⟨fp,cp,acc,rev,digits,p11.trans mod0,p3.trans mod1,p12.trans inverse,p13,p14⟩
  obtain ⟨q,nq,rq,sq,iq,aq⟩ := four_rounds ctx state ip
  obtain ⟨u,nu,ru,fu,cu,iu,wu,au⟩ :=
    Correction.correct ctx sq.frame sq.constants iq sq.modulus0 sq.modulus1
  have value : ReverseWordsAt u (exponentFrameBase s) (squareReducedWords a) := by
    change ReverseWordsAt u _ (Correction.words
      (Square.Reduction.Body.Correction.reduce
        ⟨(squareWords a).first,(squareWords a).second,(squareWords a).top.low,(squareWords a).top.mid⟩
        (squareWords a).top.high))
    simpa only [Correction.inputLimbs,sq.accumulator.1,sq.accumulator.2.1,
      sq.accumulator.2.2.1,sq.accumulator.2.2.2.1,sq.accumulator.2.2.2.2] using wu
  have countq : (Operand.mem (exponentFrameBase s + 0x7c) : Operand 32).read q = BitVec.ofNat 32 k :=
    (round_read aq (by decide) (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans count
  have slotq : (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read q =
      (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read t :=
    (round_read aq (by decide) (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans slot
  exact ⟨u,_,(rp.trans rq).trans ru,fu,cu,iu,
    (au.read (r := 11) (n := 64) (by simp [Correction.components])).trans sq.modulus0,
    (au.read (r := 3) (n := 64) (by simp [Correction.components])).trans sq.modulus1,
    (au.read (r := 12) (n := 64) (by simp [Correction.components])).trans sq.inverse,
    value,(Correction.saved_counter au).trans countq,(Correction.saved_window au).trans slotq,
    ((ap.trans (round_agrees_broad aq)).trans (Correction.agrees_wide au)).mono (by simp)⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour
