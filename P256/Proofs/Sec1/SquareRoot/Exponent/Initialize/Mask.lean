import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import P256.Proofs.Common.Lift.Generated.Values

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_mask [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x115445)
    (count : t.regValue .rcx=2) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ u.RIP=0x115454 ∧
      u.regValue .rax=3 ∧ AgreesExcept [.reg 0,.flags,.rip] t u := by
  obtain ⟨a,a1,r1,e1⟩ := (mov_r32_imm32_effect_step 0x115445 0xb8 (by decide) 14).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x15445 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1544a (by decide)))
  have g1 : AgreesExcept [.reg 0,.rip] t a := e1.agrees
  have f1 := frame.after_registers r1 g1 (by simp [Component.Covers]) (by simp)
  have v1 : a.regValue .rax=14 := e1.writes
  have c1 : a.regValue .rcx=2 := (g1.read (n := 64) (r := 1) (by simp)).trans count
  obtain ⟨b,a2,r2,e2⟩ := (shr_r64_cl_effect_step 0x11544a 0x48 0xe8 (by decide) rfl rfl).advances
    (readyToStep f1.machine f1.bindingsSupported)
    (programText_slice (programLoaded_codeIn f1.loaded) 0x1544a _ (by decide) (by decide +kernel))
    e1.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1544d (by decide)))
  have g2 : AgreesExcept [.reg 0,.flags,.rip] a b := e2.agrees
  have f2 := f1.after_registers r2 g2 (by simp [Component.Covers]) (by simp)
  have v2 : b.regValue .rax=3 := by
    have h : b.regValue .rax=a.regValue .rax >>> shiftCount 64 ((a.regValue .rcx).setWidth 8) := e2.writes
    rw [v1,c1] at h
    exact h
  have c2 : b.regValue .rcx=2 := (g2.read (n := 64) (r := 1) (by simp)).trans c1
  obtain ⟨c,a3,r3,e3⟩ := (shl_r64_cl_effect_step 0x11544d 0x48 0xe0 (by decide) rfl rfl).advances
    (readyToStep f2.machine f2.bindingsSupported)
    (programText_slice (programLoaded_codeIn f2.loaded) 0x1544d _ (by decide) (by decide +kernel))
    e2.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15450 (by decide)))
  have g3 : AgreesExcept [.reg 0,.flags,.rip] b c := e3.agrees
  have f3 := f2.after_registers r3 g3 (by simp [Component.Covers]) (by simp)
  have v3 : c.regValue .rax=12 := by
    have h : c.regValue .rax=b.regValue .rax <<< shiftCount 64 ((b.regValue .rcx).setWidth 8) := e3.writes
    rw [v2,c2] at h
    exact h
  obtain ⟨u,a4,r4,e4⟩ := (xor_r64_imm8_effect_step 0x115450 0x48 0xf0 15 (by decide) rfl rfl).advances
    (readyToStep f3.machine f3.bindingsSupported)
    (programText_slice (programLoaded_codeIn f3.loaded) 0x15450 _ (by decide) (by decide +kernel))
    e3.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15454 (by decide)))
  have g4 : AgreesExcept [.reg 0,.flags,.rip] c u := e4.agrees
  refine ⟨u,((a1.trans a2).trans a3).trans a4,
    f3.after_registers r4 g4 (by simp [Component.Covers]) (by simp),e4.rip,?_,?_⟩
  · have h : u.regValue .rax=c.regValue .rax ^^^ 15 := e4.writes
    rw [v3] at h
    exact h
  · exact (((g1.trans g2).trans g3).trans g4).mono (by simp)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
