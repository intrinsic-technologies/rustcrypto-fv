import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Loop
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Setup
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Finish
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem square_four_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x n a : Nat} (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (rip : t.RIP = 0x1154d6) (acc : Field.MontgomeryAt t (exponentFrameBase s + 0x30) a) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentPosition s u x n ∧
      u.RIP = 0x11586c ∧ Field.MontgomeryAt u (exponentFrameBase s + 0x30)
        (a ^ 16 % P256.Spec.Operations.domain.p) := by
  open SquareFour in
  obtain ⟨v,ha,hf,hc,hi,hrax,hbx,hr11,hr12,hsave,h0,h1,h2,h3,hag⟩ :=
    setup ctx hp.frame hp.constants rip
  let l := Field.readLimbs t (exponentFrameBase s + 0x30)
  let limbs : Vector (BitVec 64) 4 := #v[l.l0,l.l1,l.l2,l.l3]
  have hreverse : SquareFour.ReverseWordsAt v (exponentFrameBase s) limbs := by
    refine ⟨h0,?_,?_,?_⟩
    · change (Operand.mem (exponentFrameBase s + 0x60) : Operand 64).read v =
        (Operand.mem ((exponentFrameBase s + 0x30) + 8) : Operand 64).read t
      rw [BitVec.add_assoc]; exact h1
    · change (Operand.mem (exponentFrameBase s + 0x58) : Operand 64).read v =
        (Operand.mem ((exponentFrameBase s + 0x30) + 16) : Operand 64).read t
      rw [BitVec.add_assoc]; exact h2
    · change (Operand.mem (exponentFrameBase s + 0x50) : Operand 64).read v =
        (Operand.mem ((exponentFrameBase s + 0x30) + 24) : Operand 64).read t
      rw [BitVec.add_assoc]; exact h3
  have hvalue : SquareFour.wordsValue limbs = a * 2^256 % P256.Spec.Operations.domain.p :=
    (SquareFour.Correction.words_value l).trans (Field.readLimbs_toNat acc.2)
  obtain ⟨w,fuel,b,ha1,hf1,hc1,hi1,hrax1,hr111,hbx1,hr121,hwords1,hvalue1,hslot1,hag1⟩ :=
    SquareFour.squares_loop ctx hf hc hi (hr11.trans hp.modulus0) hbx (hr12.trans hp.inverse)
      hrax hreverse hvalue 4 (by decide)
  have hpre : AgreesExcept (SquareFour.components (exponentFrameBase s)) t w :=
    (hag.trans hag1).mono (by simp)
  have hword : exponentWordAt w (exponentFrameBase s + 0x2c0) (BitVec.ofNat 64 (n/16)) :=
    (SquareFour.word_of_agrees hpre 0x2c0 (by decide) (by unfold SquareFour.scratchOffset; omega)).trans hp.savedWord
  have hwindow : exponentWordAt w (exponentFrameBase s + 0x2d0) (BitVec.ofNat 64 (n%16)) :=
    hslot1.trans (hsave.trans hp.window)
  obtain ⟨u,ha2,hf2,hc2,hi2,h152,hbx2,h132,h112,h122,hbp2,h142,h02,h12,h22,h32,hag2⟩ :=
    SquareFour.finish ctx hf1 hc1 hi1
  have htotal : AgreesExcept (SquareFour.components (exponentFrameBase s)) t u :=
    (hpre.trans hag2).mono (by simp)
  have hallocated := SquareFour.stack_readable ctx hf2 (offset := 0x30) (len := 32) (by decide) (by decide)
  refine ⟨u,_,(ha.trans ha1).trans ha2,
    ⟨hf2,hc2,hbp2.trans hword,
      (SquareFour.word_of_agrees htotal 0x2c0 (by decide) (by unfold SquareFour.scratchOffset; omega)).trans hp.savedWord,
      h142.trans hwindow,hbx2,h132,h152,h112.trans hr111,h122.trans hr121⟩,hi2,?_⟩
  have hn : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At u (exponentFrameBase s + 0x30)
      (Field.readLimbs u (exponentFrameBase s + 0x30)).toNat := Field.nat256At_readLimbs hallocated.mem
  have out0 : memLoad u.external (exponentFrameBase s + 0x30) 64 = b[0] :=
    h02.trans hwords1.1
  have out1 : memLoad u.external (exponentFrameBase s + 0x30 + 8) 64 = b[1] := by
    rw [BitVec.add_assoc]
    exact h12.trans hwords1.2.1
  have out2 : memLoad u.external (exponentFrameBase s + 0x30 + 16) 64 = b[2] := by
    rw [BitVec.add_assoc]
    exact h22.trans hwords1.2.2.1
  have out3 : memLoad u.external (exponentFrameBase s + 0x30 + 24) 64 = b[3] := by
    rw [BitVec.add_assoc]
    exact h32.trans hwords1.2.2.2
  have hl : Field.readLimbs u (exponentFrameBase s + 0x30) =
      (⟨b[0],b[1],b[2],b[3]⟩ : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) := by
    unfold Field.readLimbs
    rw [out0,out1,out2,out3]
  rw [hl] at hn
  have hvnat : (⟨b[0],b[1],b[2],b[3]⟩ : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs).toNat =
      SquareFour.wordsValue b := (SquareFour.Correction.words_value _).symm
  rw [hvnat,hvalue1] at hn
  exact ⟨Nat.mod_lt _ Field.Montgomery.p_pos,by simpa only [Nat.mod_mul_mod] using hn⟩

end P256.Proofs.Sec1.SquareRoot
