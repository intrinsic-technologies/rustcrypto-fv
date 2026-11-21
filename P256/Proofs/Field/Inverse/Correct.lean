import P256.Proofs.Field.Inverse.Setup.CoreResult
import P256.Proofs.Field.Inverse.Tail
import P256.Proofs.Field.Inverse.SafeGcd.Core

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Operations P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Projective.Algebra (modulus_pos inverse_zero)
open Standards.SECG.ECC X86.Machine X86.UserProcess

theorem inverse_correct_of_core [Bindings]
    (nonzeroCore : ∀ {s : RamState} {boundary : ReturnBoundary} {a : Nat},
      SafeGcdPre s boundary → Nat256At s (s.regValue .rsi) a →
      0 < a → a < domain.p → ∃ t, SafeGcd.Core.NonzeroResult s t boundary a)
    (zeroCore : ∀ {s : RamState} {boundary : ReturnBoundary},
      SafeGcdPre s boundary → Nat256At s (s.regValue .rsi) 0 →
      ∃ t, SafeGcd.Core.ZeroResult s t boundary)
    {s : RamState} {boundary : ReturnBoundary} {z : Nat}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) z) :
    ∃ t, CalleeResult s t boundary 40 880 ∧
      MontgomeryAt t (s.regValue .rdi) (Curve.inverse domain.p z) ∧
      t.external[s.regValue .rdi + 32]? = some (if z = 0 then 0 else 1) := by
  by_cases hz : z = 0
  · subst z
    rw [inverse_zero]
    obtain ⟨n,t,run,state,rip,flag⟩ := inverse_zero_core_of_contract zeroCore pre input
    obtain ⟨u,result,output,flagOut⟩ := inverse_tail_selected
      (select := false) (value := 0) pre state rip flag (by intro h; cases h) run
    refine ⟨u,result,⟨modulus_pos,?_⟩,?_⟩
    · simpa only [Nat.zero_mul, Nat.zero_mod, Bool.false_eq_true,
        ↓reduceIte] using output
    · exact flagOut
  · obtain ⟨n,t,run,state,rip,value,flag⟩ :=
      inverse_nonzero_core_of_contract nonzeroCore pre input hz
    obtain ⟨u,result,output,flagOut⟩ := inverse_tail_selected
      (select := true) (value := Curve.inverse domain.p z * 2^256 % domain.p)
      pre state rip flag (fun _ ↦ value.2) run
    rw [ite_eq_left rfl] at output flagOut
    refine ⟨u,result,⟨value.1,output⟩,?_⟩
    rw [ite_eq_right hz]
    exact flagOut

theorem inverse_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {z : Nat}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) z) :
    ∃ t, CalleeResult s t boundary 40 880 ∧
      MontgomeryAt t (s.regValue .rdi) (Curve.inverse domain.p z) ∧
      t.external[s.regValue .rdi + 32]? = some (if z = 0 then 0 else 1) :=
  inverse_correct_of_core SafeGcd.Core.nonzero_correct SafeGcd.Core.zero_correct pre input

end P256.Proofs.Field.Inverse
