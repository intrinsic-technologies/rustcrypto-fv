import P256.Proofs.Sec1Serialize.Tail.Initialize.Choice
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem prepare_index (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) (rip : t.RIP = 0x11118e)
    (rax : t.regValue .rax = if infinity then 1 else 0) : ∃ u, SelectionEntry s u boundary bytes infinity := by
  have code1 : CodeIn (codeRange 0x11118e [0x31, 0xd2]) t :=
    programText_slice (programLoaded_codeIn h.state.loaded) 0x1118e _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := xor_r32_r32_effect_step 0x11118e 0xd2
    (by decide) t (readyToStep h.state.machine h.state.bindingsSupported) code1 rip
  change (xorR32R32Effect 0x11118e 2 2 2 t).Holds t t1 at effect1
  have h1 := h.after_registers pre step1 ready1 effect1
    (by simp [Component.Covers]) (by simp) (by simp)
    (inProgram_of_textOffset 0x11190 (by decide))
  have a1 : t1.regValue .rax = if infinity then 1 else 0 := (effect1.agrees.read (n := 64) (r := 0) (by simp)).trans rax
  have d1 : t1.regValue .rdx = 0 := by
    have eq := effect1.writes
    change t1.regValue .rdx = (((Operand.reg 2 : Operand 32).read t) ^^^
      ((Operand.reg 2 : Operand 32).read t)).setWidth 64 at eq
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at eq
    exact eq.trans (by rfl)
  have code2 : CodeIn (codeRange 0x111190 [0x48, 0x8d, 0x4c, 0x24, 0x0b]) t1 :=
    programText_slice (programLoaded_codeIn h1.state.loaded) 0x11190 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := lea_r64_effect_step 0x111190 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl
    t1 ready1 code2 effect1.rip
  change (leaR64Effect 0x111190 1 (.sib 4 none 0 (.d8 11)) t1).Holds t1 t2 at effect2
  have h2 := h1.after_registers pre step2 ready2 effect2
    (by simp [Component.Covers]) (by simp) (by simp)
    (inProgram_of_textOffset 0x11195 (by decide))
  have a2 : t2.regValue .rax = if infinity then 1 else 0 := (effect2.agrees.read (n := 64) (r := 0) (by simp)).trans a1
  have d2 : t2.regValue .rdx = 0 := (effect2.agrees.read (n := 64) (r := 2) (by simp)).trans d1
  have code3 : CodeIn (codeRange 0x111195
      (encodeNopM [0x66,0x66,0x2e] (.sib 0 (some 0) 0 (.d32 0)))) t2 :=
    programText_slice (programLoaded_codeIn h2.state.loaded) 0x11195 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, step3, ready3, effect3⟩ := nop_m_effect_step 0x111195 [0x66,0x66,0x2e]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl
    t2 ready2 code3 effect2.rip
  change (nopEffect 0x111195 11).Holds t2 u at effect3
  have h3 := h2.after_registers pre step3 ready3 effect3
    (by simp [nopEffect, Effect.components, Component.Covers])
    (by simp [nopEffect, Effect.components]) (by simp [nopEffect, Effect.components])
    (inProgram_of_textOffset 0x111a0 (by decide))
  have a3 : u.regValue .rax = if infinity then 1 else 0 := (effect3.agrees.read (n := 64) (r := 0)
    (by simp [nopEffect, Effect.components])).trans a2
  have d3 : u.regValue .rdx = 0 := (effect3.agrees.read (n := 64) (r := 2)
    (by simp [nopEffect, Effect.components])).trans d2
  refine ⟨u, h3.state, h3.execution, effect3.rip, ?_, d3, h3.destination, h3.source, h3.zeroSource⟩
  rw [a3]
  cases infinity <;> rfl

end P256.Proofs.Sec1Serialize
