import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Progress
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Finish

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open ProjectiveRadix
open Recenter (rawDigit)

theorem extraction_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d 32)
    (rip : t.RIP = 0x10ba22) :
    ∃ fuel u, Advances boundary fuel t u ∧ NibbleState s u d ∧
      AgreesExcept (digitComponents s) t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := extraction_finish_block boundary pre.outerBoundary t
    (state.ready)
    (programText_slice (programLoaded_codeIn (state.toState.loaded pre)) 0xba22 extractionFinishBytes
      (by decide +kernel) (by decide +kernel)) rip
  have agrees : AgreesExcept (digitComponents s) t u :=
    effect.agrees.mono (by simp [extractionFinishEffect,Effect.components,digitComponents])
  have external := effect.agrees.external (by simp [extractionFinishEffect,Effect.components,Component.Covers])
  refine ⟨fuel,u,run,⟨frame_after_digits pre state.toState ready agrees,effect.rip,?_,?_,?_⟩,agrees⟩
  · intro i hi
    change memLoad u.external _ 8 = _
    rw [external]
    by_cases h : i < 64
    · exact state.digits i h
    · have he : i = 64 := by omega
      subst i
      have addr : stackPtr s - 112 + BitVec.ofNat 64 64 = stackPtr s - 48 := by
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [addr]
      exact state.last
  · exact (effect.agrees.read (n := 8) (r := 0)
      (by simp [extractionFinishEffect,Effect.components])).trans (state.rax (by decide))
  · exact effect.writes

end P256.Proofs.Projective.Multiply.Machine.Radix
