import P256.Proofs.Signing.Core.State
import P256.Proofs.Common.Machine.Divergence

set_option autoImplicit false

namespace P256.Proofs.Signing.Core

open P256.Spec P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Machine

theorem loop_correct (nextNonce : NextNonceContract) (iteration : IterationContract)
    [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {secret attempts : Nat} {digest : ByteArray} {signature : Nat × Nat} {state : Nonce.State}
    (pre : SignPre s boundary) (input : SignInput s secret digest)
    (loop : Loop s t state) (rip : t.RIP = 0x10caa5)
    (execution : ∃ fuel, Advances boundary fuel s t)
    (signed : Search.signingAttempts secret digest attempts state = some signature) :
    ∃ u, CalleeResult s u boundary 65 4584 ∧
      Nat256At u (s.regValue .rdi) signature.1 ∧
      Nat256At u (s.regValue .rdi + 32) signature.2 := by
  induction attempts using Nat.strongRecOn generalizing t state with
  | ind attempts ih =>
      obtain ⟨nonce, final, found, reference⟩ := Search.exists_firstValid_of_signingAttempts signed
      obtain ⟨_, a, _, runA, ripA, candidate⟩ := nextNonce.1 pre loop rip found
      obtain ⟨_, initialRun⟩ := execution
      obtain ⟨_, b, runB, result⟩ :=
        iteration pre input candidate ripA ⟨_, initialRun.trans runA⟩
      have executionB : ∃ fuel, Advances boundary fuel s b :=
        ⟨_, (initialRun.trans runA).trans runB⟩
      rcases result with ⟨failed, ripB, next⟩ | ⟨output, success, returned, first, second⟩
      · rcases reference with immediate | ⟨_, remaining, smaller, later⟩
        · rw [failed] at immediate
          cases immediate
        · exact ih remaining smaller next ripB executionB later
      · have same : signature = output := by
          rcases reference with immediate | ⟨failed, _, _, _⟩
          · exact Option.some.inj (immediate.symm.trans success)
          · rw [failed] at success
            cases success
        subst output
        exact ⟨b, returned, first, second⟩

theorem loop_diverges (nextNonce : NextNonceContract) (iteration : IterationContract)
    [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {secret : Nat} {digest : ByteArray} {state : Nonce.State}
    (pre : SignPre s boundary) (input : SignInput s secret digest)
    (loop : Loop s t state) (rip : t.RIP = 0x10caa5)
    (execution : ∃ fuel, Advances boundary fuel s t)
    (exhausted : ∀ attempts, Search.signingAttempts secret digest attempts state = none) :
    Prelude.Diverges boundary t [] := by
  classical
  let invariant := fun u => ∃ current,
    Loop s u current ∧ u.RIP = 0x10caa5 ∧ (∃ fuel, Advances boundary fuel s u) ∧
      ∀ attempts, Search.signingAttempts secret digest attempts current = none
  apply diverges_of_progress (invariant := invariant) ?_
    ⟨state, loop, rip, execution, exhausted⟩
  intro u member
  obtain ⟨current, currentLoop, currentRip, ⟨initialFuel, initialRun⟩, currentExhausted⟩ := member
  by_cases hasNonce : ∃ nonce final, Search.FirstValid current nonce final
  · obtain ⟨nonce, final, found⟩ := hasNonce
    have noSignature := found.signingAttempts_none currentExhausted
    obtain ⟨steps, a, positive, runA, ripA, candidate⟩ :=
      nextNonce.1 pre currentLoop currentRip found
    obtain ⟨tail, b, runB, result⟩ :=
      iteration pre input candidate ripA ⟨_, initialRun.trans runA⟩
    rcases result with ⟨_, ripB, next⟩ | ⟨_, signature, _, _, _⟩
    · exact Or.inl ⟨steps + tail, b, by omega, runA.trans runB,
        final, next, ripB, ⟨initialFuel + steps + tail, (initialRun.trans runA).trans runB⟩,
        noSignature.2⟩
    · rw [noSignature.1] at signature
      cases signature
  · exact Or.inr (nextNonce.2 pre currentLoop currentRip hasNonce)

end P256.Proofs.Signing.Core
