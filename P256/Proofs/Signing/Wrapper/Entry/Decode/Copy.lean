import P256.Proofs.Signing.Wrapper.Entry.Decode.Copy.Result

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_correct [Bindings] {boundary : ReturnBoundary} {input : ByteArray} {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : CopyPre input s) : ∃ t, CopyResult boundary input s t := by
  obtain ⟨fuel, t, ht, rt, _, he⟩ := Copy.run boundary outside input s ready
    (programText_slice (programLoaded_codeIn loaded) 0x23c9 Copy.bytes
      (by decide +kernel) (by decide +kernel)) pre
  have hf := Copy.frame he
  refine ⟨t, ⟨⟨fuel, ht⟩, rt, ?_, he.rip, ?_, hf, Copy.hasBytes pre he, hf.grow⟩⟩
  · intro a b hb
    rw [hf.memory]
    · exact loaded a b hb
    · intro c hc ha
      simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨i, hi, rfl⟩ := ha
      exact pre.avoids _ (pre.contains hi) (.inl ⟨b, hb⟩)
  · exact hf.read (n := 64) (r := 4) (by simp [copyComponents])

end P256.Proofs.Signing.Wrapper.Entry.Decode
