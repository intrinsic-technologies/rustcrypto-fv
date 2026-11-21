import P256.Proofs.Signing.Wrapper.State
import P256.Proofs.Common.Machine.Divergence

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem wrapper_of_contracts (entryCorrect : EntryContract) (hashCorrect : HashContract)
    (finishCorrect : FinishContract) : WrapperContract := by
  intro core bindings initial secret message supported machine call
  have ctx : Context initial secret message := ⟨supported, machine, call⟩
  obtain ⟨s, entry⟩ := entryCorrect ctx
  have hash := hashCorrect core entry
  have model (attempts : Nat) :
      Ecdsa.signMessageWithin attempts #[secret, message] =
        (Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
          (Operations.hash message) .empty).map (fun signature => some (Ecdsa.encodeFixed signature)) := by
    rfl
  constructor
  · intro attempts bytes found
    rw [model] at found
    cases hs : Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
        (Operations.hash message) .empty with
    | none => simp [hs] at found
    | some signature =>
      have encoded : Ecdsa.encodeFixed signature = bytes := by simpa only
        [hs, Option.map_some, Option.some.injEq] using found
      obtain ⟨t, result⟩ := hash.1 attempts signature hs
      rw [← encoded]
      exact finishCorrect ctx result.toSerializedInput
  · intro exhausted
    have hnone : ∀ attempts, Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
        (Operations.hash message) .empty = none := by
      intro attempts
      have absent := exhausted attempts
      rw [model] at absent
      exact Option.map_eq_none_iff.mp absent
    obtain ⟨fuel, run⟩ := entry.execution
    obtain ⟨slices, hcall⟩ := call
    exact ⟨returnBoundary initial, initial_boundary hcall machine supported,
      Common.Machine.diverges_of_advances run (hash.2 hnone)⟩

end P256.Proofs.Signing.Wrapper
