import P256.Proofs.Signing.Core.Iteration.Components.SecondProduct
import P256.Proofs.Signing.Core.Iteration.Components.ConstructorSetupRun
import P256.Proofs.Signing.Core.Iteration.Components.ConstructorCall

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce x y : Nat} {digest : ByteArray} (constructor : ConstructorContract)
    (hp : SignPre s boundary) (original : SignInput s secret digest)
    (positive : 0 < nonce) (canonical : nonce < Operations.domain.n)
    (affine : Curve.scalarMul Operations.domain nonce Operations.domain.G = .affine x y)
    (input : Products s t state secret nonce x y digest) (rip : t.RIP = 0x10d2f0) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d33e ∧
      Computed s u state secret nonce digest x y := by
  obtain ⟨na,a,runA,frameA,ea⟩ := ConstructorSetup.run hp input.frame rip
  have valuesA := input.values.copy (fun off live => ConstructorSetup.byte input.frame ea
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have regsA : Registers s a := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (ea.agrees.read (n := 64) (r := 5) (by simp [ConstructorSetup.effect,Effect.components])).trans input.registers.rbp
    · exact (ea.agrees.read (n := 64) (r := 13) (by simp [ConstructorSetup.effect,Effect.components])).trans input.registers.r13
    · exact (ea.agrees.read (n := 64) (r := 14) (by simp [ConstructorSetup.effect,Effect.components])).trans input.registers.r14
    · exact (ea.agrees.read (n := 64) (r := 15) (by simp [ConstructorSetup.effect,Effect.components])).trans input.registers.r15
  have rA : Nat256At a (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) input.value (fun i hi => ConstructorSetup.byte input.frame ea
      (by omega) (.inl (by omega)))
  have second : Nat256At a (frameBase s+2096) (scalarS secret nonce x digest) :=
    nat256_copy (offset := 2096) input.product (fun i hi => ConstructorSetup.byte input.frame ea
      (by omega) (.inr (by omega)))
  have first := ConstructorSetup.copied hp input.frame frameA ea input.value
  obtain ⟨nb,b,runB,frameB,ripB,result,memB,regB⟩ := constructor_call constructor
    (Nat.mod_lt _ (by decide +kernel)) (Nat.mod_lt _ (by decide +kernel)) hp frameA ea.rip
    (ea.writes.2.2.2.1.trans input.registers.r15)
    (ea.writes.2.2.2.2.1.trans input.rbx)
    (ea.writes.2.2.1.trans input.registers.rbp) first second
  have valuesB := valuesA.copy (fun off live => memB off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have regsB := regsA.copy regB
  have rB : Nat256At b (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) rA (fun i hi => memB _ (by omega) (.inl (by omega)))
  have result' : ConstructorResult b (frameBase s+528) (x % Operations.domain.n)
      (scalarS secret nonce x digest) := result
  have model : Ecdsa.signWithNonce secret nonce digest =
      if x % Operations.domain.n == 0 || scalarS secret nonce x digest == 0 then none
      else some (x % Operations.domain.n, scalarS secret nonce x digest) :=  signWithNonce_of_affine original.positive original.canonical positive canonical
    original.digest.1 affine
  refine ⟨na+nb,b,runA.trans runB,ripB,
    ⟨frameB,valuesB.arguments,valuesB.generator,valuesB.point,rB,
      regsB.rbp,regsB.r13,regsB.r14,regsB.r15,?_⟩⟩
  by_cases zero : x % Operations.domain.n = 0 ∨ scalarS secret nonce x digest = 0
  · have guard : (x % Operations.domain.n == 0 || scalarS secret nonce x digest == 0) = true := by
      simpa only [Bool.or_eq_true,beq_iff_eq] using zero
    rw [guard] at model
    have rejected : memLoad b.external (frameBase s+528) 64 = 1 ∧
        memLoad b.external (frameBase s+528+8) 64 = 0 := by
      have h : ConstructorResult b (frameBase s+528) (x % Operations.domain.n)
          (scalarS secret nonce x digest) := result'
      unfold ConstructorResult at h
      rw [ite_eq_left zero] at h
      exact h
    refine .inl ⟨model,rejected.1,?_⟩
    have h := rejected.2
    simp only [BitVec.add_assoc,BitVec.reduceAdd] at h
    exact h
  · have guard : ¬ (x % Operations.domain.n == 0 || scalarS secret nonce x digest == 0) = true := by
      simpa only [Bool.or_eq_true,beq_iff_eq] using zero
    rw [ite_eq_right guard] at model
    have accepted : memLoad b.external (frameBase s+528) 64 = 0 ∧
        Nat256At b (frameBase s+528+8) (x % Operations.domain.n) ∧
        Nat256At b (frameBase s+528+40) (scalarS secret nonce x digest) := by
      have h : ConstructorResult b (frameBase s+528) (x % Operations.domain.n)
          (scalarS secret nonce x digest) := result'
      unfold ConstructorResult at h
      rw [ite_eq_right zero] at h
      exact h
    refine .inr ⟨(x % Operations.domain.n,scalarS secret nonce x digest),model,accepted.1,?_,?_⟩
    · have h := accepted.2.1
      simp only [BitVec.add_assoc,BitVec.reduceAdd] at h
      exact h
    · have h := accepted.2.2
      simp only [BitVec.add_assoc,BitVec.reduceAdd] at h
      exact h

end P256.Proofs.Signing.Core.Iteration.Components
