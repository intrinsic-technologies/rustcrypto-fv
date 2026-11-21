import P256.Proofs.Signing.Core.Iteration.Components.FirstProduct
import P256.Proofs.Signing.Core.Iteration.Components.ScalarCalls
import P256.Proofs.Signing.Core.Iteration.Components.AddSetupRun
import P256.Proofs.Signing.Core.Iteration.Components.InverseSetupRun
import P256.Proofs.Signing.Core.Iteration.Components.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

structure Products [Bindings] (s t : RamState) (state : Nonce.State) (secret nonce x y : Nat)
    (digest : ByteArray) : Prop extends Reduced s t state nonce x y digest where
  product : Nat256At t (frameBase s+2096) (scalarS secret nonce x digest)
  rbx : t.regValue .rbx = frameBase s+2096

theorem second_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce x y : Nat} {digest : ByteArray} (add : AddContract) (hp : SignPre s boundary)
    (input : Multiplied s t state secret nonce x y digest) (rip : t.RIP = 0x10d2c2) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d2f0 ∧
      Products s u state secret nonce x y digest := by
  obtain ⟨na,a,runA,frameA,ea⟩ := AddSetup.run hp input.frame rip
  have memoryA := ea.agrees.external (by simp [AddSetup.effect,Effect.components,Component.Covers])
  have valuesA := input.values.copy (fun off _ => congrArg (·[_]?) memoryA)
  have rA : Nat256At a (frameBase s+176) (x % Operations.domain.n) :=
    ⟨input.value.1,fun i hi => by rw [memoryA]; exact input.value.2 i hi⟩
  have prodA : Nat256At a (frameBase s+1328)
      ((x % Operations.domain.n)*secret % Operations.domain.n) :=
    ⟨input.product.1,fun i hi => by rw [memoryA]; exact input.product.2 i hi⟩
  have regsA : Registers s a := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (ea.agrees.read (n := 64) (r := 5) (by simp [AddSetup.effect,Effect.components])).trans input.registers.rbp
    · exact (ea.agrees.read (n := 64) (r := 13) (by simp [AddSetup.effect,Effect.components])).trans input.registers.r13
    · exact (ea.agrees.read (n := 64) (r := 14) (by simp [AddSetup.effect,Effect.components])).trans input.registers.r14
    · exact (ea.agrees.read (n := 64) (r := 15) (by simp [AddSetup.effect,Effect.components])).trans input.registers.r15
  obtain ⟨nb,b,runB,frameB,ripB,sumB,memB,regB⟩ := add_call add
    (Nat.mod_lt _ (by decide +kernel)) (Nat.mod_lt _ (by decide +kernel)) hp frameA ea.rip
    (ea.writes.2.1.trans (congrArg (·+1296) input.frame.rsp))
    (ea.writes.2.2.trans input.registers.r15)
    (ea.writes.1.trans input.registers.rbp) valuesA.digest prodA
  have valuesB := valuesA.copy (fun off live => memB off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have regsB := regsA.copy regB
  have rB : Nat256At b (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) rA (fun i hi => memB _ (by omega) (.inl (by omega)))
  obtain ⟨nc,c,runC,frameC,ec⟩ := InverseSetup.run hp frameB ripB
  have memoryC := ec.agrees.external (by simp [InverseSetup.effect,Effect.components,Component.Covers])
  have valuesC := valuesB.copy (fun off _ => congrArg (·[_]?) memoryC)
  have rC : Nat256At c (frameBase s+176) (x % Operations.domain.n) :=
    ⟨rB.1,fun i hi => by rw [memoryC]; exact rB.2 i hi⟩
  have sumC : Nat256At c (frameBase s+528)
      ((Arith.uint digest % Operations.domain.n+
        (x % Operations.domain.n*secret) % Operations.domain.n) % Operations.domain.n) :=
    ⟨sumB.1,fun i hi => by rw [memoryC]; exact sumB.2 i hi⟩
  have regsC : Registers s c := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (ec.agrees.read (n := 64) (r := 5) (by simp [InverseSetup.effect,Effect.components])).trans regsB.rbp
    · exact (ec.agrees.read (n := 64) (r := 13) (by simp [InverseSetup.effect,Effect.components])).trans regsB.r13
    · exact (ec.agrees.read (n := 64) (r := 14) (by simp [InverseSetup.effect,Effect.components])).trans regsB.r14
    · exact (ec.agrees.read (n := 64) (r := 15) (by simp [InverseSetup.effect,Effect.components])).trans regsB.r15
  have bxC : c.regValue .rbx = frameBase s+2096 :=
    ec.writes.1.trans (congrArg (·+2096) frameB.rsp)
  obtain ⟨nd,d,runD,frameD,ripD,prodD,memD,regD⟩ := inverse_product hp frameC ec.rip
    (ec.writes.2.2.1.trans (congrArg (·+336) frameB.rsp))
    (ec.writes.2.2.2.trans regsB.rbp)
    (ec.writes.2.1.trans (congrArg (·+2096) frameB.rsp)) valuesC.inverse sumC
  have valuesD := valuesC.copy (fun off live => memD off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have rD : Nat256At d (frameBase s+176) (x % Operations.domain.n) :=
    nat256_copy (offset := 176) rC (fun i hi => memD _ (by omega) (.inl (by omega)))
  exact ⟨na+nb+nc+nd,d,((runA.trans runB).trans runC).trans runD,ripD,
    ⟨⟨frameD,valuesD,regsC.copy regD,rD⟩,prodD,(regD .rbx (by simp)).trans bxC⟩⟩

end P256.Proofs.Signing.Core.Iteration.Components
