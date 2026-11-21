import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Select0
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Select1
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Select2
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Select3
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Representation

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

def words (a : Limbs) : Vector (BitVec 64) 4 := #v[a.l0,a.l1,a.l2,a.l3]

theorem words_value (a : Limbs) : wordsValue (words a) = a.toNat := by
  simp [words,wordsValue,Limbs.toNat,P256.Proofs.Field.Montgomery.wordBase,
    Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc]

def selectEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq select0Effect select1Effect) select2Effect) select3Effect

theorem select_local : Effect.Local selectEffect :=
  ((select0_local.seq select1_local).seq select2_local).seq select3_local

theorem select_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x11579b) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (selectEffect t).Holds t u ∧ AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨t1,n1,r1,f1,e1,a1⟩ := select0_run ctx hf hip
  obtain ⟨t2,n2,r2,f2,e2,a2⟩ := select1_run ctx f1 e1.rip
  obtain ⟨t3,n3,r3,f3,e3,a3⟩ := select2_run ctx f2 e2.rip
  obtain ⟨t4,n4,r4,f4,e4,a4⟩ := select3_run ctx f3 e3.rip
  have h2 := e1.seq select1_local (select0_local.full t) e2
  have h3 := h2.seq select2_local ((select0_local.seq select1_local).full t) e3
  have h4 := h3.seq select3_local (((select0_local.seq select1_local).seq select2_local).full t) e4
  exact ⟨t4,_,((r1.trans r2).trans r3).trans r4,f4,h4,trans (trans (trans a1 a2) a3) a4⟩

theorem select_values [Bindings] {s t u : RamState}
    (hf : ExponentFrame s t) (hh : (selectEffect t).Holds t u) :
    ReverseWordsAt u (exponentFrameBase s)
      (words (selectLimbs
        ⟨(Operand.reg 1 : Operand 64).read t, (Operand.reg 5 : Operand 64).read t,
          (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read t,
          (Operand.reg 13 : Operand 64).read t⟩
        ⟨(Operand.reg 0 : Operand 64).read t, (Operand.reg 2 : Operand 64).read t,
          (Operand.reg 6 : Operand 64).read t, (Operand.reg 7 : Operand 64).read t⟩
        (((Operand.reg 8 : Operand 8).read t).setWidth 64))) := by
  have hsp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  have ho := hh.obsAfter (select_local.full t) true
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [← ho.read_mem]
  all_goals x86_norm [selectEffect,select0Effect,select1Effect,select2Effect,select3Effect,
    words,selectLimbs,selectWord,hsp]
  all_goals rfl

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
