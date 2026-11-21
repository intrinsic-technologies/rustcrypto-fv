import P256.Proofs.Program.CalleeRegisters
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Negate

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1137d0 32 32 24) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = 0x113f20 ∧ t.regValue .rdx = s.regValue .rsi ∧
      t.regValue .rsi = 0x202620 ∧ AgreesExcept [.reg 2,.reg 6,.rip] s t := by
  obtain ⟨t, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step 0x1137d0 0x48 0xf2 (by simp [RexWPrefix]) rfl).advances
      (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x137d0 _ (by decide) (by decide +kernel))
      pre.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137d3 (by decide)))
  have ag1 : AgreesExcept [.reg 2,.rip] s t := effect.agrees
  have mem : t.external = s.external := ag1.external (by simp [Component.Covers])
  have loaded : ProgramLoaded t := by simpa only [ProgramLoaded,mem] using pre.loaded
  obtain ⟨u, run', ready', effect'⟩ :=
    (mov_r64_imm32_effect_step 0x1137d3 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202620).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x137d3 _ (by decide) (by decide +kernel))
      effect.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137da (by decide)))
  have ag2 : AgreesExcept [.reg 6,.rip] t u := effect'.agrees
  have mem' : u.external = t.external := ag2.external (by simp [Component.Covers])
  have loaded' : ProgramLoaded u := by simpa only [ProgramLoaded,mem'] using loaded
  obtain ⟨v, run'', ready'', effect''⟩ :=
    (jmp_rel32_effect_step 0x1137da 1857 (by decide +kernel)).advances
      ready' (programText_slice (programLoaded_codeIn loaded') 0x137da _ (by decide) (by decide +kernel))
      effect'.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13f20 (by decide)))
  have ag3 : AgreesExcept [.rip] u v := effect''.agrees
  have ag : AgreesExcept [.reg 2,.reg 6,.rip] s v := by
    apply ((ag1.trans ag2).trans ag3).mono
    simp
  refine ⟨v,(run.trans run').trans run'',ready'',effect''.rip,?_,?_,ag⟩
  · have a : t.regValue .rdx = s.regValue .rsi := effect.writes
    have b : u.regValue .rdx = t.regValue .rdx := ag2.read (n := 64) (r := 2) (by simp)
    exact (ag3.read (n := 64) (r := 2) (by simp)).trans (b.trans a)
  · have a : u.regValue .rsi = 0x202620 := effect'.writes
    exact (ag3.read (n := 64) (r := 6) (by simp)).trans a

end P256.Proofs.Projective.Multiply.Machine.Lookup.Negate
