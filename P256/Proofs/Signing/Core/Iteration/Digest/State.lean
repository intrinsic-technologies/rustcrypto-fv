import P256.Proofs.Signing.Core.Iteration.Candidate

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SecretKeyFromBytes.Scalar

def LiveOffset (i : Nat) : Prop :=
  (72 ≤ i ∧ i < 104) ∨ (272 ≤ i ∧ i < 336) ∨ (2160 ≤ i ∧ i < 2232)

def Preserved (s t u : RamState) : Prop :=
  ∀ i, LiveOffset i → u.external[frameBase s + BitVec.ofNat 64 i]? =
    t.external[frameBase s + BitVec.ofNat 64 i]?

structure NonceState [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  scalar : Nat256At t (frameBase s + 304) nonce
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

theorem NonceState.copy [Bindings] {s t u : RamState} {state : Nonce.State} {nonce : Nat}
    (input : NonceState s t state nonce) (frame : Frame s u) (memory : Preserved s t u)
    (registers : ∀ reg ∈ [.rbp, .r13, .r14, .r15], u.regValue reg = t.regValue reg) :
    NonceState s u state nonce := by
  have bytes (offset len : Nat) (range : ∀ i < len, LiveOffset (offset+i)) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memory _ (range i hi)
  refine ⟨frame, NextNonce.arguments_copy input.arguments (fun i range => memory i (.inl range)),
    input.generator.copy (bytes 2160 72 (by intro i hi; unfold LiveOffset; omega))
      ⟨input.generator.2.1.1, fun i hi =>
        (bytes 272 32 (by intro j hj; unfold LiveOffset; omega) i hi).trans (input.generator.2.1.2 i hi)⟩,
    ⟨input.scalar.1, fun i hi =>
      (bytes 304 32 (by intro j hj; unfold LiveOffset; omega) i hi).trans (input.scalar.2 i hi)⟩,
    input.positive, input.canonical,
    (registers .rbp (by simp)).trans input.rbp,
    (registers .r13 (by simp)).trans input.r13,
    (registers .r14 (by simp)).trans input.r14,
    (registers .r15 (by simp)).trans input.r15⟩

end P256.Proofs.Signing.Core.Iteration.Digest
