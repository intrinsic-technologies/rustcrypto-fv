import P256.Proofs.Generate.Sampler.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program

theorem prepare_zero [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c6c) (decoded : t.regValue .r15 = stackPtr t+80) :
    ∃ u, Advances boundary 2 t u ∧ State s u ∧ u.RIP = 0x100c77 ∧
      u.regValue .rdi = stackPtr u + 184 ∧ u.regValue .rsi = stackPtr u + 80 ∧
      AgreesExcept [.reg 7,.reg 6,.rip] t u := by
  obtain ⟨a,ha,ra,ea⟩ :=
    (lea_r64_effect_step 0x100c6c 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xc6c _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc74 (by decide)))
  have fa : AgreesExcept [.reg 7,.rip] t a := ea.agrees
  have sa := state.after_registers pre ra fa (by simp [Component.Covers]) (by simp)
  obtain ⟨u,hu,ru,eu⟩ :=
    (mov_r64_r64_effect_step 0x100c74 0x4c 0xfe (by simp [RexWPrefix]) rfl).advances ra
      (programText_slice (programLoaded_codeIn sa.loaded) 0xc74 _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc77 (by decide)))
  have fu : AgreesExcept [.reg 6,.rip] a u := eu.agrees
  have su := sa.after_registers pre ru fu (by simp [Component.Covers]) (by simp)
  have sp : stackPtr u = stackPtr t := (fa.trans fu).read (n := 64) (r := 4) (by simp)
  refine ⟨u,ha.trans hu,su,eu.rip,?_,?_,(fa.trans fu).mono (by simp)⟩
  · rw [sp]
    exact (fu.read (n := 64) (r := 7) (by simp)).trans ea.writes
  · rw [sp]
    exact eu.writes.trans ((fa.read (n := 64) (r := 15) (by simp)).trans decoded)

end P256.Proofs.Generate.Sampler.Nonzero
