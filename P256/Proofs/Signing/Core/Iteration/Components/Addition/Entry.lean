import P256.Proofs.Signing.Core.Iteration.Components.Addition.State
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset
  programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x113920 ∧ AgreesExcept [.reg 1, .rip] s t ∧
      t.regValue .rcx = 0x2025e0 := by
  obtain ⟨u, hu, ready, effect⟩ :=
    (mov_r64_imm32_effect_step 0x113310 0x48 0xc1
      (by simp [RexWPrefix]) rfl rfl 0x2025e0).advances
      (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x13310 _
        (by decide +kernel) (by decide +kernel)) pre.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13317 (by decide)))
  change (movR64Imm32Effect 0x113310 1 0x2025e0 s).Holds s u at effect
  have memory : u.external = s.external := effect.agrees.external (by simp [Component.Covers])
  have loaded : ProgramLoaded u := by
    intro a b h
    rw [memory]
    exact pre.loaded a b h
  obtain ⟨t, ht, final, jump⟩ :=
    (jmp_rel32_effect_step 0x113317 0x604 (by decide +kernel)).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x13317 _
        (by decide +kernel) (by decide +kernel)) effect.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13920 (by decide)))
  have agrees : AgreesExcept [.reg 1, .rip] s t :=
    (effect.agrees.trans jump.agrees).mono (by simp)
  refine ⟨t, hu.trans ht, final, ?_, jump.rip, agrees, ?_⟩
  · intro a b h
    rw [agrees.external (by simp [Component.Covers])]
    exact pre.loaded a b h
  · exact (jump.agrees.read (n := 64) (r := 1) (by simp)).trans effect.writes

end P256.Proofs.Signing.Core.Iteration.Components.Addition
