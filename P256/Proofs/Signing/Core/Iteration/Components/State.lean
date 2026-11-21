import P256.Proofs.Signing.Core.Iteration.Stages
import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

def LiveOffset (offset : Nat) : Prop :=
  (72 ≤ offset ∧ offset < 169) ∨
    (272 ≤ offset ∧ offset < 368) ∨ (1296 ≤ offset ∧ offset < 1328) ∨
    (2160 ≤ offset ∧ offset < 2232)

def Preserved (s t u : RamState) : Prop :=
  ∀ offset, LiveOffset offset →
    u.external[frameBase s+BitVec.ofNat 64 offset]? =
      t.external[frameBase s+BitVec.ofNat 64 offset]?

structure Values (s t : RamState) (state : Nonce.State) (nonce x y : Nat)
    (digest : ByteArray) : Prop where
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s+2160) (frameBase s+272) state
  point : Sec1.AffineAt t (frameBase s+104) (.affine x y)
  inverse : Nat256At t (frameBase s+336) (Curve.inverse Operations.domain.n nonce)
  digest : Nat256At t (frameBase s+1296) (Arith.uint digest % Operations.domain.n)

theorem nat256_copy {s t u : RamState} {offset x : Nat}
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x)
    (copy : ∀ i < 32, u.external[frameBase s+BitVec.ofNat 64 (offset+i)]? =
      t.external[frameBase s+BitVec.ofNat 64 (offset+i)]?) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  have h := copy i hi
  rw [BitVec.ofNat_add,← BitVec.add_assoc] at h
  exact h.trans (value.2 i hi)

theorem Values.copy {s t u : RamState} {state : Nonce.State} {nonce x y : Nat}
    {digest : ByteArray} (values : Values s t state nonce x y digest)
    (copy : Preserved s t u) : Values s u state nonce x y digest := by
  refine ⟨NextNonce.arguments_copy values.arguments (fun off live =>
    copy off (by unfold LiveOffset; omega)),?_,?_,?_,?_⟩
  · apply values.generator.copy
    · intro i hi
      have h := copy (2160+i) (.inr (.inr (.inr ⟨by omega,by omega⟩)))
      simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using h
    · exact nat256_copy values.generator.2.1 (fun i hi =>
        copy (272+i) (.inr (.inl ⟨by omega,by omega⟩)))
  · apply values.point.of_bytes_eq
    intro i hi
    have h := copy (104+i) (.inl ⟨by omega,by omega⟩)
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using h
  · exact nat256_copy values.inverse (fun i hi =>
      copy (336+i) (.inr (.inl ⟨by omega,by omega⟩)))
  · exact nat256_copy values.digest (fun i hi =>
      copy (1296+i) (.inr (.inr (.inl ⟨by omega,by omega⟩))))

structure Registers (s t : RamState) : Prop where
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r14 : t.regValue .r14 = frameBase s+2160
  r15 : t.regValue .r15 = frameBase s+1328

theorem Registers.copy {s t u : RamState} (regs : Registers s t)
    (copy : ∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
      u.regValue reg = t.regValue reg) : Registers s u :=
  ⟨(copy .rbp (by simp)).trans regs.rbp,(copy .r13 (by simp)).trans regs.r13,
    (copy .r14 (by simp)).trans regs.r14,(copy .r15 (by simp)).trans regs.r15⟩

end P256.Proofs.Signing.Core.Iteration.Components
