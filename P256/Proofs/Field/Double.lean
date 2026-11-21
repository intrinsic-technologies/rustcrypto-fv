import P256.Proofs.Field.Double.Entry
import P256.Proofs.Field.Add.Correct

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem field_double_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x : Nat} (pre : CalleePre s boundary 0x1137f0 32 32 16)
    (input : MontgomeryAt s (s.regValue .rsi) x) :
    ∃ u, CalleeResult s u boundary 32 16 ∧
      MontgomeryAt u (s.regValue .rdi) ((x + x) % Operations.domain.p) := by
  obtain ⟨t, run, child, agrees, right⟩ := Double.enter pre
  have memory := agrees.external (by simp [Component.Covers])
  have source : t.regValue .rsi = s.regValue .rsi :=
    agrees.read (n := 64) (r := 6) (by simp)
  have destination : t.regValue .rdi = s.regValue .rdi :=
    agrees.read (n := 64) (r := 7) (by simp)
  have represented : MontgomeryAt t (t.regValue .rsi) x := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, memory, source] using input
  obtain ⟨u, result, value⟩ := field_add_body_correct child represented (right ▸ represented)
  have saved : CalleeSavedRegistersUnchanged s t := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 3) (by simp)
    · exact agrees.read (n := 64) (r := 5) (by simp)
    · exact agrees.read (n := 64) (r := 12) (by simp)
    · exact agrees.read (n := 64) (r := 13) (by simp)
    · exact agrees.read (n := 64) (r := 14) (by simp)
    · exact agrees.read (n := 64) (r := 15) (by simp)
  exact ⟨u, result.prepend_registers run memory
    (agrees.read (n := 64) (r := 4) (by simp)) destination saved
    (agrees.mxcsr (by simp)) (agrees.fcw (by simp)), destination ▸ value⟩

end P256.Proofs.Field
