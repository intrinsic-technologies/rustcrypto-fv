import P256.Proofs.Nonce.Fill.Tail.Decode.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x107567)
    (shift : s.regValue .r14 = 0) (destination : s.regValue .r12 = stackPtr s + 8) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x107575 ∧
      t.regValue .rdi = stackPtr s + 8 ∧ t.regValue .rsi = stackPtr s + 152 ∧
      t.regValue .rdx = 0 ∧ AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] s t := by
  obtain ⟨a, aa, ar, ae⟩ :=
    (mov_r64_r64_effect_step 0x107567 0x4c 0xe7 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x7567 _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x756a (by decide)))
  have ag : AgreesExcept [.reg 7, .rip] s a := ae.agrees
  have av : a.regValue .rdi = stackPtr s + 8 := (show a.regValue .rdi = s.regValue .r12 from ae.writes).trans destination
  have am := ag.external (by simp [Component.Covers])
  obtain ⟨b, ba, br, be⟩ :=
    (lea_r64_effect_step 0x10756a 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl).advances ar
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq am) 0x756a _
        (by decide +kernel) (by decide +kernel)) ae.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7572 (by decide)))
  have bg : AgreesExcept [.reg 6, .rip] a b := be.agrees
  have bv : b.regValue .rsi = stackPtr s + 152 := by
    have h : b.regValue .rsi = stackPtr a + 152 := be.writes
    rw [show stackPtr a = stackPtr s from ag.read (n := 64) (r := 4) (by simp)] at h
    exact h
  have bm := (bg.external (by simp [Component.Covers])).trans am
  obtain ⟨t, ta, tr, te⟩ := (mov_r32_r32_rex_effect_step 0x107572 0x44 0xf2 (by simp [RexNoWPrefix]) rfl).advances br
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq bm) 0x7572 _
      (by decide +kernel) (by decide +kernel)) be.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x7575 (by decide)))
  have tg : AgreesExcept [.reg 2, .rip] b t := te.agrees
  refine ⟨t, (aa.trans ba).trans ta, tr, te.rip,
    ((bg.trans tg).read (n := 64) (r := 7) (by simp)).trans av,
    (tg.read (n := 64) (r := 6) (by simp)).trans bv, ?_,
    ((ag.trans bg).trans tg).mono (by simp)⟩
  have bp : b.regValue .r14 = 0 := ((ag.trans bg).read (n := 64) (r := 14) (by simp)).trans shift
  have h : t.regValue .rdx = ((b.regValue .r14).setWidth 32).setWidth 64 := te.writes
  simpa [bp] using h

end P256.Proofs.Nonce.Fill.Tail.Decode
