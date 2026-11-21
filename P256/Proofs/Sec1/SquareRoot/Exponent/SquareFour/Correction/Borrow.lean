import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Low
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Middle
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.High
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Top

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

def inputLimbs (t : RamState) : Limbs :=
  ⟨(Operand.reg 1 : Operand 64).read t, (Operand.reg 5 : Operand 64).read t,
    (Operand.reg 8 : Operand 64).read t, (Operand.reg 9 : Operand 64).read t⟩

def borrowEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq lowEffect middleEffect) highEffect) topEffect

theorem borrow_local : Effect.Local borrowEffect :=
  ((low_local.seq middle_local).seq high_local).seq top_local

theorem borrow_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x11568e) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (borrowEffect t).Holds t u ∧ AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨t1,n1,r1,f1,e1,a1⟩ := low_run ctx hf hip
  obtain ⟨t2,n2,r2,f2,e2,a2⟩ := middle_run ctx f1 e1.rip
  obtain ⟨t3,n3,r3,f3,e3,a3⟩ := high_run ctx f2 e2.rip
  obtain ⟨t4,n4,r4,f4,e4,a4⟩ := top_run ctx f3 e3.rip
  have h2 := e1.seq middle_local (low_local.full t) e2
  have h3 := h2.seq high_local ((low_local.seq middle_local).full t) e3
  have h4 := h3.seq top_local (((low_local.seq middle_local).seq high_local).full t) e4
  exact ⟨t4,_,((r1.trans r2).trans r3).trans r4,f4,h4,trans (trans (trans a1 a2) a3) a4⟩

theorem borrow_values [Bindings] {s t u : RamState} {x : Nat}
    (hf : ExponentFrame s t) (hc : ExponentConstants s t x)
    (mod0 : (Operand.reg 11 : Operand 64).read t = -1)
    (mod1 : (Operand.reg 3 : Operand 64).read t = 0xffffffff)
    (hh : (borrowEffect t).Holds t u) :
    (Operand.reg 0 : Operand 64).read u = (subRaw (inputLimbs t) modulus).1.l0 ∧
    (Operand.reg 2 : Operand 64).read u = (subRaw (inputLimbs t) modulus).1.l1 ∧
    (Operand.reg 6 : Operand 64).read u = (subRaw (inputLimbs t) modulus).1.l2 ∧
    (Operand.reg 7 : Operand 64).read u = (subRaw (inputLimbs t) modulus).1.l3 ∧
    (Operand.reg 9 : Operand 64).read u = -(subRaw (inputLimbs t) modulus).2 ∧
    (Operand.reg 13 : Operand 64).read u = (inputLimbs t).l3 ∧
    (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read u = (inputLimbs t).l2 ∧
    (Operand.reg 1 : Operand 64).read u = (inputLimbs t).l0 ∧
    (Operand.reg 5 : Operand 64).read u = (inputLimbs t).l1 := by
  have hsp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  have hm2 : (Operand.mem (exponentFrameBase s + 0x98#64) : Operand 64).read t = 0 := hc.modulus2
  have hm3 : (Operand.mem (exponentFrameBase s + 0x90#64) : Operand 64).read t = 0xffffffff00000001 := hc.modulus3
  have ho := hh.obsAfter (borrow_local.full t) true
  simp only [BitVec.ofNat_eq_ofNat] at mod0 mod1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | rw [← ho.read_reg] | rw [← ho.read_mem]
  all_goals x86_norm [borrowEffect,lowEffect,middleEffect,highEffect,topEffect,hsp,hm2,hm3,
    mod0,mod1,subRaw,subWord,borrow,modulus,inputLimbs,BitVec.xor_self,BitVec.zero_sub]
  all_goals rfl

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
