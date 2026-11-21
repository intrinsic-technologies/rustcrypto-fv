import P256.Proofs.Nonce.Initialize.Prepare.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Read

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10798d)
    (shift : s.regValue .rbp = 0) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x107999 ∧
      t.regValue .rdi = stackPtr s + 8 ∧ t.regValue .rsi = stackPtr s + 72 ∧
      t.regValue .rdx = 0 ∧ AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] s t := by
  obtain ⟨a, aa, ar, ae⟩ :=
    (lea_r64_effect_step 0x10798d 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x798d _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7992 (by decide)))
  have ag : AgreesExcept [.reg 7, .rip] s a := ae.agrees
  have av : a.regValue .rdi = stackPtr s + 8 := ae.writes
  have am := ag.external (by simp [Component.Covers])
  obtain ⟨b, ba, br, be⟩ :=
    (lea_r64_effect_step 0x107992 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl).advances ar
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq am) 0x7992 _
        (by decide +kernel) (by decide +kernel)) ae.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7997 (by decide)))
  have bg : AgreesExcept [.reg 6, .rip] a b := be.agrees
  have bv : b.regValue .rsi = stackPtr s + 72 := by
    have h : b.regValue .rsi = stackPtr a + 72 := be.writes
    rw [show stackPtr a = stackPtr s from ag.read (n := 64) (r := 4) (by simp)] at h
    exact h
  have bm := (bg.external (by simp [Component.Covers])).trans am
  obtain ⟨t, ta, tr, te⟩ := (mov_r32_r32_effect_step 0x107997 0xea rfl).advances br
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq bm) 0x7997 _
      (by decide +kernel) (by decide +kernel)) be.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x7999 (by decide)))
  have tg : AgreesExcept [.reg 2, .rip] b t := te.agrees
  refine ⟨t, (aa.trans ba).trans ta, tr, te.rip,
    ((bg.trans tg).read (n := 64) (r := 7) (by simp)).trans av,
    (tg.read (n := 64) (r := 6) (by simp)).trans bv, ?_,
    ((ag.trans bg).trans tg).mono (by simp)⟩
  have bp : b.regValue .rbp = 0 := ((ag.trans bg).read (n := 64) (r := 5) (by simp)).trans shift
  have h : t.regValue .rdx = ((b.regValue .rbp).setWidth 32).setWidth 64 := te.writes
  simpa [bp] using h

end P256.Proofs.Nonce.Initialize.Read
