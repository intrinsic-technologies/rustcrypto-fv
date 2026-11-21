import P256.Proofs.Verifying.Core.Reduce.Memory
import P256.Proofs.Program.ScalarFrame.Prologue
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11312e ∧ stackPtr t = stackPtr s - 88 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, ha, hr, hl, hip, hsp, hm, hf⟩ :=
    save_registers pre.stack (pre.avoids (Stack.region s 104) (by simp))
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide) (codeOffset := 0x13120) pre.rip (by constructor <;> decide +kernel)
  obtain ⟨t, hstep, hrt, het⟩ :=
    sub_r64_imm8_effect_step 0x11312a 0x48 0xec 40
      (by unfold RexWPrefix; decide +kernel) rfl rfl u hr
      (programText_slice (programLoaded_codeIn hl) 0x1312a
        [0x48,0x83,0xec,0x28] (by decide +kernel) rfl) hip
  have hip' : t.RIP = 0x11312e := het.rip
  have hat : Advances boundary 1 u t := Advances.of_step hstep (.inl (by
    rw [hip']
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1312e (by decide))))
  have hext : t.external = u.external := het.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, ha.trans hat, hrt, ?_, het.rip, ?_, hext.trans hm, ?_⟩
  · intro a b hab
    rw [hext]
    exact hl a b hab
  · have hwrite : stackPtr t = stackPtr u - 40 := het.writes
    rw [hwrite, hsp, BitVec.sub_sub]
    rfl
  · apply (hf.trans het.agrees).mono
    simp only [saveFrame, subR64Imm8Effect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact .inl h
    · exact .inl (.inl rfl)
    · exact .inr rfl
    · exact .inl (.inr (.inl rfl))

end P256.Proofs.Verifying.Core.Reduce
