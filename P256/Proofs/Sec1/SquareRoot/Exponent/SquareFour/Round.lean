import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundFrame
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundSemantics
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundStart
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Counter

set_option autoImplicit false
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure RoundState [Bindings] (s t : RamState) (x : Nat) (a : Vector (BitVec 64) 4)
    (acc : FinalWords) (k : Nat) : Prop where
  frame : ExponentFrame s t
  constants : ExponentConstants s t x
  accumulator : AccumulatorAt t acc
  words : ReverseWordsAt t (exponentFrameBase s) a
  digits : ∀ i : Fin 4,
    (Operand.mem (exponentFrameBase s + 0x10 + BitVec.ofNat 64 (8*i.val)) : Operand 64).read t = a[i]
  modulus0 : (Operand.reg 11 : Operand 64).read t = 0xffffffffffffffff
  modulus1 : (Operand.reg 3 : Operand 64).read t = 0xffffffff
  inverse : (Operand.reg 12 : Operand 64).read t = 0xffffffffffffffff
  index : (Operand.reg 13 : Operand 64).read t = BitVec.ofNat 64 k
  zero : (Operand.reg 14 : Operand 64).read t = 0

theorem round_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x k : Nat}
    {a : Vector (BitVec 64) 4} {old : FinalWords}
    (ctx : ExponentPre s boundary x) (hs : RoundState s t x a old k)
    (hip : t.RIP = 0x115550) (hk : k < 4) :
    ∃ u fuel, Advances boundary fuel t u ∧
      RoundState s u x a (squareRound old a[(⟨k,hk⟩ : Fin 4)] a) (k+1) ∧
      u.RIP = (if k = 3 then 0x11568e else 0x115550) ∧
      AgreesExcept (roundComponents (exponentFrameBase s)) t u := by
  obtain ⟨v, e1, hf1, hip1, hsi, hax, hlo, hmid, ha1⟩ :=
    round_start ctx hs.frame hip hk hs.index
  have hb1 : AgreesExcept (roundComponents (exponentFrameBase s)) t v := ha1.mono (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, roundComponents] at hc ⊢
    grind only)
  have hc1 := constants_of_agrees ctx hs.constants (round_agrees_broad hb1)
  have hw1 := round_reverse hb1 hs.words
  have hdsi : (Operand.reg 6 : Operand 64).read v = a[(⟨k,hk⟩ : Fin 4)] := hsi.trans (hs.digits ⟨k,hk⟩)
  have hdax : (Operand.reg 0 : Operand 64).read v = a[(⟨k,hk⟩ : Fin 4)] := hax.trans hdsi
  have hac1 := hs.accumulator.of_agrees ha1 (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hbp1 : (Operand.reg 11 : Operand 64).read v = 0xffffffffffffffff :=
    (ha1.read (by simp)).trans hs.modulus0
  have hr131 : (Operand.reg 3 : Operand 64).read v = 0xffffffff :=
    (ha1.read (by simp)).trans hs.modulus1
  have hinverse1 : (Operand.reg 12 : Operand 64).read v = 0xffffffffffffffff :=
    (ha1.read (by simp)).trans hs.inverse
  have hzero1 : (Operand.reg 14 : Operand 64).read v = 0 :=
    (ha1.read (by simp)).trans hs.zero
  have hlow1 : (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read v = old.top.low :=
    hlo.trans hs.accumulator.2.2.1
  have hmid1 : (Operand.mem (exponentFrameBase s + 0x2f0) : Operand 64).read v = old.top.mid :=
    hmid.trans hs.accumulator.2.2.2.1
  obtain ⟨w, n2, e2, hf2, he2⟩ := arithmetic_run ctx hf1 hip1
  have hac2 := arithmetic_accumulator hf1 hc1 a a[(⟨k,hk⟩ : Fin 4)] old hw1 hac1 hinverse1 hdax hdsi
    hbp1 hr131 hzero1 hlow1 hmid1 he2
  have hinverse2 := arithmetic_inverse hf1 hc1 he2
  have hmods := arithmetic_moduli hf1 hc1 he2
  have hb2 := arithmetic_agrees hf1.rsp he2
  have hindex2 : (Operand.reg 13 : Operand 64).read w = BitVec.ofNat 64 k :=
    (arithmetic_index he2).trans ((ha1.read (by simp)).trans hs.index)
  obtain ⟨u, e3, hr3, hip3, hi3, hz3, ha3⟩ := inner_counter
    (readyToStep hf2.machine hf2.bindingsSupported) (programLoaded_codeIn hf2.loaded)
    ctx.outerBoundary he2.rip hk hindex2
  have hb3 : AgreesExcept (roundComponents (exponentFrameBase s)) w u := ha3.mono (by
    simp [roundComponents])
  have hb : AgreesExcept (roundComponents (exponentFrameBase s)) t u :=
    ((hb1.trans hb2).trans hb3).mono (by simp)
  have hf3 := frame_of_agrees ctx hf2 hr3 (round_agrees_broad hb3)
  refine ⟨u, _, (e1.trans e2).trans e3, ?_, hip3, hb⟩
  refine ⟨hf3, constants_of_agrees ctx hs.constants (round_agrees_broad hb), ?_,
    round_reverse hb hs.words, ?_, ?_, ?_, ?_, hi3, hz3⟩
  · exact hac2.of_agrees ha3 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  · intro i
    have h60 := (show ∀ i : Fin 4, OffsetsApart 0x2f0 8 (0x10+BitVec.ofNat 64 (8*i.val)) 8 by
      unfold OffsetsApart; decide +kernel) i
    have hd8 := (show ∀ i : Fin 4, OffsetsApart 0x2e8 8 (0x10+BitVec.ofNat 64 (8*i.val)) 8 by
      unfold OffsetsApart; decide +kernel) i
    have he0 := (show ∀ i : Fin 4, OffsetsApart 0x70 8 (0x10+BitVec.ofNat 64 (8*i.val)) 8 by
      unfold OffsetsApart; decide +kernel) i
    rw [BitVec.add_assoc, round_read hb (by decide) h60 hd8 he0, ← BitVec.add_assoc]
    exact hs.digits i
  · exact (ha3.read (by simp)).trans hmods.1
  · exact (ha3.read (by simp)).trans hmods.2
  · exact (ha3.read (by simp)).trans hinverse2

theorem four_rounds [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    {a : Vector (BitVec 64) 4}
    (ctx : ExponentPre s boundary x)
    (hs : RoundState s t x a ⟨0,0,⟨0,0,0,0,false⟩⟩ 0)
    (hip : t.RIP = 0x115550) :
    ∃ u fuel, Advances boundary fuel t u ∧ RoundState s u x a (squareWords a) 4 ∧
      u.RIP = 0x11568e ∧ AgreesExcept (roundComponents (exponentFrameBase s)) t u := by
  obtain ⟨t1,n1,e1,h1,i1,a1⟩ := round_correct ctx hs hip (by decide)
  obtain ⟨t2,n2,e2,h2,i2,a2⟩ := round_correct ctx h1 (by simpa using i1) (by decide)
  obtain ⟨t3,n3,e3,h3,i3,a3⟩ := round_correct ctx h2 (by simpa using i2) (by decide)
  obtain ⟨u,n4,e4,h4,i4,a4⟩ := round_correct ctx h3 (by simpa using i3) (by decide)
  exact ⟨u,_,((e1.trans e2).trans e3).trans e4,h4,by simpa using i4,
    (((a1.trans a2).trans a3).trans a4).mono (by simp)⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour
