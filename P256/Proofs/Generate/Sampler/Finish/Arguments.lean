import P256.Proofs.Generate.Sampler.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program

theorem prepare_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100d45) :
    ∃ u, Advances boundary 2 t u ∧ State s u ∧ u.RIP = 0x100d4f ∧
      u.regValue .rdi = stackPtr u + 112 ∧ u.regValue .rsi = stackPtr u + 40 ∧
      u.external = t.external ∧ stackPtr u = stackPtr t := by
  obtain ⟨a,ha,ra,ea⟩ :=
    (lea_r64_effect_step 0x100d45 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xd45 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4a (by decide)))
  have fa : AgreesExcept [.reg 7,.rip] t a := ea.agrees
  have sa := state.after_registers pre ra fa (by simp [Component.Covers]) (by simp)
  obtain ⟨u,hu,ru,eu⟩ :=
    (lea_r64_effect_step 0x100d4a 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances ra
      (programText_slice (programLoaded_codeIn sa.loaded) 0xd4a _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4f (by decide)))
  have fu : AgreesExcept [.reg 6,.rip] a u := eu.agrees
  have su := sa.after_registers pre ru fu (by simp [Component.Covers]) (by simp)
  have sp : stackPtr u = stackPtr t := (fa.trans fu).read (n := 64) (r := 4) (by simp)
  refine ⟨u,ha.trans hu,su,eu.rip,?_,?_,(fa.trans fu).external (by simp [Component.Covers]),sp⟩
  · rw [sp]
    exact (fu.read (n := 64) (r := 7) (by simp)).trans ea.writes
  · have h : u.regValue .rsi = stackPtr a + 40 := eu.writes
    have spu : stackPtr u = stackPtr a := fu.read (n := 64) (r := 4) (by simp)
    rw [h,spu]

theorem prepare_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100d7c)
    (pointer : memLoad t.external (stackPtr t + 72) 64 = s.regValue .rdi) :
    ∃ u, Advances boundary 4 t u ∧ State s u ∧ u.RIP = 0x100d8e ∧
      u.regValue .rsi = stackPtr u + 80 ∧ u.regValue .rcx = 13 ∧
      u.regValue .rdi = s.regValue .rdi ∧ u.regValue .rax = s.regValue .rdi ∧
      u.external = t.external ∧ stackPtr u = stackPtr t := by
  obtain ⟨a,ha,ra,ea⟩ :=
    (lea_r64_effect_step 0x100d7c 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xd7c _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd81 (by decide)))
  have fa : AgreesExcept [.reg 6,.rip] t a := ea.agrees
  have sa := state.after_registers pre ra fa (by simp [Component.Covers]) (by simp)
  obtain ⟨b,hb,rb,eb⟩ := (mov_r32_imm32_effect_step 0x100d81 0xb9 (by decide) 13).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0xd81 _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd86 (by decide)))
  have fb : AgreesExcept [.reg 1,.rip] a b := eb.agrees
  have sb := sa.after_registers pre rb fb (by simp [Component.Covers]) (by simp)
  obtain ⟨c,hc,rc,ec⟩ :=
    (mov_r64_m64_effect_step 0x100d86 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl).advances rb
      (programText_slice (programLoaded_codeIn sb.loaded) 0xd86 _
        (by decide) (by decide +kernel)) ⟨eb.rip,sb.stack_readable pre (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd8b (by decide)))
  have fc : AgreesExcept [.reg 0,.rip] b c := ec.agrees
  have sc := sb.after_registers pre rc fc (by simp [Component.Covers]) (by simp)
  obtain ⟨u,hu,ru,eu⟩ :=
    (mov_r64_r64_effect_step 0x100d8b 0x48 0xc7 (by simp [RexWPrefix]) rfl).advances rc
      (programText_slice (programLoaded_codeIn sc.loaded) 0xd8b _
        (by decide) (by decide +kernel)) ec.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd8e (by decide)))
  have fu : AgreesExcept [.reg 7,.rip] c u := eu.agrees
  have su := sc.after_registers pre ru fu (by simp [Component.Covers]) (by simp)
  have f := ((fa.trans fb).trans fc).trans fu
  have sp : stackPtr u = stackPtr t := f.read (n := 64) (r := 4) (by simp)
  have ax : c.regValue .rax = s.regValue .rdi := by
    have h : c.regValue .rax = memLoad b.external (stackPtr b + 72) 64 := ec.writes
    have spb : stackPtr b = stackPtr t := (fa.trans fb).read (n := 64) (r := 4) (by simp)
    rw [h,(fa.trans fb).external (by simp [Component.Covers]),spb]
    exact pointer
  refine ⟨u,((ha.trans hb).trans hc).trans hu,su,eu.rip,?_,?_,?_,?_,
    f.external (by simp [Component.Covers]),sp⟩
  · rw [sp]
    exact (((fb.trans fc).trans fu).read (n := 64) (r := 6) (by simp)).trans ea.writes
  · exact ((fc.trans fu).read (n := 64) (r := 1) (by simp)).trans eb.writes
  · exact eu.writes.trans ax
  · exact (fu.read (n := 64) (r := 0) (by simp)).trans ax

end P256.Proofs.Generate.Sampler.Finish
