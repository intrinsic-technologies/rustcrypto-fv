import P256.Proofs.Verifying.Core.Output.Branch
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem accept [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e170)
    (readable : MemReadable s (stackPtr s+384) 8) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e191 ∧
      t.regValue .rcx = 0 ∧ t.regValue .rax = memLoad s.external (stackPtr s+384) 64 ∧
      AgreesExcept [.reg 0,.reg 1,.flags,.rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ := (xor_r32_r32_effect_step 0x10e170 0xc9 rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0xe170 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe172 (by decide)))
  have fa : AgreesExcept [.reg 1, .flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have zero : a.regValue .rcx = 0 := by
    have h : a.regValue .rcx =
        (((s.regValue .rcx).setWidth 32 ^^^ (s.regValue .rcx).setWidth 32).setWidth 64) := ea.writes
    rw [h, BitVec.xor_self]
    rfl
  obtain ⟨b,hb,rb,eb⟩ := (mov_r64_m64_effect_step 0x10e172 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe172 _
      (by decide) (by decide +kernel))
    ⟨ea.rip,by
      have sp : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by simp)
      change MemReadable a (stackPtr a+384) 8
      rw [sp]
      exact readable.of_external_eq ma⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xe17a (by decide)))
  have fb : AgreesExcept [.reg 0,.rip] a b := eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have value : b.regValue .rax = memLoad s.external (stackPtr s+384) 64 := by
    have sp : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by simp)
    have hw : b.regValue .rax = memLoad a.external (stackPtr a+384) 64 := eb.writes
    simpa only [ma,sp] using hw
  obtain ⟨t, ht, rt, et⟩ := (jmp_rel8_effect_step 0x10e17a 0x15 (by decide)).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq (mb.trans ma)) 0xe17a _
      (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe191 (by decide)))
  have ft : AgreesExcept [.rip] b t := et.agrees
  exact ⟨t,(ha.trans hb).trans ht,rt,et.rip,
    ((fb.trans ft).read (n := 64) (r := 1) (by simp)).trans zero,
    (ft.read (n := 64) (r := 0) (by simp)).trans value,
    ((fa.trans fb).trans ft).mono (by simp)⟩

end P256.Proofs.Verifying.Core.Output
