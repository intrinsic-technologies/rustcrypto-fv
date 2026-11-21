import P256.Proofs.Signing.Core.Iteration.Components.ReduceX
import P256.Proofs.Signing.Core.Iteration.Components.MultiplySetupRun
import P256.Proofs.Signing.Core.Iteration.Components.ExternalProduct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

structure Multiplied [Bindings] (s t : RamState) (state : Nonce.State) (secret nonce x y : Nat)
    (digest : ByteArray) : Prop extends Reduced s t state nonce x y digest where
  product : Nat256At t (frameBase s+1328) ((x % Operations.domain.n)*secret % Operations.domain.n)

theorem first_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce x y : Nat} {digest : ByteArray} (hp : SignPre s boundary)
    (original : SignInput s secret digest) (input : Reduced s t state nonce x y digest)
    (rip : t.RIP = 0x10d272) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d2c2 ∧
      Multiplied s u state secret nonce x y digest := by
  obtain ⟨na,a,runA,frameA,ea⟩ := MultiplySetup.run hp input.frame rip
  have valuesA := input.values.copy (fun off live => MultiplySetup.byte input.frame ea
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have regsA : Registers s a := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (ea.agrees.read (n := 64) (r := 5) (by simp [MultiplySetup.effect,Effect.components])).trans input.registers.rbp
    · exact (ea.agrees.read (n := 64) (r := 13) (by simp [MultiplySetup.effect,Effect.components])).trans input.registers.r13
    · exact (ea.agrees.read (n := 64) (r := 14) (by simp [MultiplySetup.effect,Effect.components])).trans input.registers.r14
    · exact (ea.agrees.read (n := 64) (r := 15) (by simp [MultiplySetup.effect,Effect.components])).trans input.registers.r15
  have rA : Nat256At a (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) input.value (fun i hi => MultiplySetup.byte input.frame ea
      (by omega) (.inl (by omega)))
  have left := MultiplySetup.copied hp input.frame frameA ea input.value
  have rhs : a.regValue .rdx = s.regValue .rsi := by
    have h := ea.writes.2.2.2.2.1
    change a.regValue .rdx = memLoad t.external (rspOf t+80) 64 at h
    have sp : rspOf t = frameBase s := input.frame.rsp
    rw [sp] at h
    exact h.trans input.values.arguments.secret
  obtain ⟨nb,b,runB,frameB,ripB,productB,memB,regB⟩ := external_product hp frameA ea.rip
    (ea.writes.2.2.2.1.trans input.registers.rbp) rhs
    (ea.writes.2.2.1.trans input.registers.r15) left original.scalar
  have valuesB := valuesA.copy (fun off live => memB off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have rB : Nat256At b (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) rA (fun i hi => memB _ (by omega) (.inl (by omega)))
  exact ⟨na+nb,b,runA.trans runB,ripB,⟨⟨frameB,valuesB,regsA.copy regB,rB⟩,productB⟩⟩

end P256.Proofs.Signing.Core.Iteration.Components
