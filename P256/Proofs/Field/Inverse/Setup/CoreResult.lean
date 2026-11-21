import P256.Proofs.Field.Inverse.Setup.Result
import P256.Proofs.Field.Inverse.SafeGcd.Core.Contract
import P256.Proofs.Field.Inverse.Value

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program.Routines P256.Spec.Operations Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

theorem inverse_nonzero_core_of_contract [Bindings]
    (core : ∀ {s : RamState} {boundary : ReturnBoundary} {a : Nat},
      SafeGcdPre s boundary → Nat256At s (s.regValue .rsi) a →
      0 < a → a < domain.p → ∃ t, SafeGcd.Core.NonzeroResult s t boundary a)
    {s : RamState} {boundary : ReturnBoundary} {z : Nat}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) z)
    (nonzero : z ≠ 0) :
    ∃ n t, Advances boundary n s t ∧ FrameState s t ∧ t.RIP = 0x11411e ∧
      MontgomeryAt t (stackPtr s - 168) (Curve.inverse domain.p z) ∧
      t.external[stackPtr s - 136]? = some 1 := by
  obtain ⟨n,t,run,child,rsp,rbx,rsi,rdi,ret,agrees,saved⟩ := inverse_safeGcd_entry pre
  have bytes : Nat256At t (t.regValue .rsi) (z * 2^256 % domain.p) := by
    rw [rsi]
    exact safeGcd_call_input pre agrees input.2
  obtain ⟨u,result,b,output,bound,product,flag⟩ := core child bytes
    (montgomery_input_positive input.1 nonzero)
    (Nat.mod_lt _ Projective.Algebra.modulus_pos)
  have state := safeGcd_call_state pre child agrees rbx saved
  obtain ⟨frame,rip⟩ := safeGcd_result_state pre state rsp rdi ret result
  obtain ⟨m,execute⟩ := result.execution
  refine ⟨n+m,u,run.trans execute,frame,rip,?_,?_⟩
  · rw [rdi] at output
    exact montgomery_result input.1 nonzero output ⟨bound,product⟩
  · rw [rdi] at flag
    have address : stackPtr s - 168 + 32 = stackPtr s - 136 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    simpa only [address] using flag

theorem inverse_zero_core_of_contract [Bindings]
    (core : ∀ {s : RamState} {boundary : ReturnBoundary},
      SafeGcdPre s boundary → Nat256At s (s.regValue .rsi) 0 →
      ∃ t, SafeGcd.Core.ZeroResult s t boundary)
    {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) 0) :
    ∃ n t, Advances boundary n s t ∧ FrameState s t ∧ t.RIP = 0x11411e ∧
      t.external[stackPtr s - 136]? = some 0 := by
  obtain ⟨n,t,run,child,rsp,rbx,rsi,rdi,ret,agrees,saved⟩ := inverse_safeGcd_entry pre
  have bytes : Nat256At t (t.regValue .rsi) 0 := by
    rw [rsi]
    apply safeGcd_call_input pre agrees
    simpa only [Nat.zero_mul, Nat.zero_mod] using input.2
  obtain ⟨u,result,flag⟩ := core child bytes
  have state := safeGcd_call_state pre child agrees rbx saved
  obtain ⟨frame,rip⟩ := safeGcd_result_state pre state rsp rdi ret result
  obtain ⟨m,execute⟩ := result.execution
  refine ⟨n+m,u,run.trans execute,frame,rip,?_⟩
  rw [rdi] at flag
  have address : stackPtr s - 168 + 32 = stackPtr s - 136 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  simpa only [address] using flag

end P256.Proofs.Field.Inverse
