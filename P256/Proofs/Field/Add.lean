import P256.Proofs.Field.Add.Correct
import P256.Proofs.Field.Jump

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem field_add_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x y : Nat} (pre : AddPre s boundary)
    (left : MontgomeryAt s (s.regValue .rsi) x)
    (right : MontgomeryAt s (s.regValue .rdx) y) :
    ∃ t, CalleeResult s t boundary 32 16 ∧
      MontgomeryAt t (s.regValue .rdi) ((x+y) % Operations.domain.p) := by
  obtain ⟨t, run, ready, effect⟩ :=
    (jmp_rel32_effect_step 0x1137c0 1611 (by decide +kernel)).advances
      (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x137c0 _
        (by decide) (by decide +kernel)) pre.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13e10 (by decide)))
  have ag : AgreesExcept [.rip] s t := effect.agrees
  have memory := ag.external (by simp [Component.Covers])
  have source : t.regValue .rsi = s.regValue .rsi := ag.read (n := 64) (r := 6) (by simp)
  have other : t.regValue .rdx = s.regValue .rdx := ag.read (n := 64) (r := 2) (by simp)
  have output : t.regValue .rdi = s.regValue .rdi := ag.read (n := 64) (r := 7) (by simp)
  have lp : MontgomeryAt t (t.regValue .rsi) x := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, memory, source] using left
  have rp : MontgomeryAt t (t.regValue .rdx) y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, memory, other] using right
  obtain ⟨u, result, value⟩ := field_add_body_correct (pre.after_rip ready ag effect.rip) lp rp
  exact ⟨u, result_prepend_rip result run ag, output ▸ value⟩

end P256.Proofs.Field
