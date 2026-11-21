import P256.Proofs.Nonce.Initialize.Prepare.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Buffer

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem arguments_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107945) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107955 ∧
      t.regValue .rdx = stackPtr s + 104 ∧ t.regValue .rcx = 4 ∧
      t.regValue .rdi = s.regValue .rax ∧
      t.regValue .r8 = ((s.regValue .r9).setWidth 32).setWidth 64 ∧
      AgreesExcept [.reg 2, .reg 1, .reg 7, .reg 8, .rip] s t := by
  obtain ⟨a, aa, ar, ae⟩ :=
    (lea_r64_effect_step 0x107945 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7945 _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x794a (by decide)))
  have ag : AgreesExcept [.reg 2, .rip] s a := ae.agrees
  have af := stage.after_registers aa ar ag (by simp [Component.Covers]) (by simp)
  have ad : a.regValue .rdx = stackPtr s + 104 := ae.writes
  obtain ⟨b, ba, br, be⟩ :=
    (mov_r32_imm32_effect_step 0x10794a 0xb9 (by decide) 4).advances ar
      (programText_slice (programLoaded_codeIn af.loaded) 0x794a _
        (by decide +kernel) (by decide +kernel)) ae.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x794f (by decide)))
  have bg : AgreesExcept [.reg 1, .rip] a b := be.agrees
  have bf := af.after_registers ba br bg (by simp [Component.Covers]) (by simp)
  have bc : b.regValue .rcx = 4 := be.writes
  obtain ⟨c, ca, cr, ce⟩ :=
    (mov_r64_r64_effect_step 0x10794f 0x48 0xc7 (by simp [RexWPrefix]) rfl).advances br
      (programText_slice (programLoaded_codeIn bf.loaded) 0x794f _
        (by decide +kernel) (by decide +kernel)) be.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7952 (by decide)))
  have cg : AgreesExcept [.reg 7, .rip] b c := ce.agrees
  have cf := bf.after_registers ca cr cg (by simp [Component.Covers]) (by simp)
  have cp : c.regValue .rdi = s.regValue .rax :=
    ce.writes.trans ((ag.trans bg).read (n := 64) (r := 0) (by simp))
  obtain ⟨t, ta, tr, te⟩ :=
    (mov_r32_r32_rex_effect_step 0x107952 0x45 0xc8 (by simp [RexNoWPrefix]) rfl).advances cr
      (programText_slice (programLoaded_codeIn cf.loaded) 0x7952 _
        (by decide +kernel) (by decide +kernel)) ce.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7955 (by decide)))
  have tg : AgreesExcept [.reg 8, .rip] c t := te.agrees
  refine ⟨t, cf.after_registers ta tr tg (by simp [Component.Covers]) (by simp), te.rip,
    ?_, ?_, ?_, ?_, (((ag.trans bg).trans cg).trans tg).mono (by simp)⟩
  · exact (((bg.trans cg).trans tg).read (n := 64) (r := 2) (by simp)).trans ad
  · exact ((cg.trans tg).read (n := 64) (r := 1) (by simp)).trans bc
  · exact (tg.read (n := 64) (r := 7) (by simp)).trans cp
  · have nine : c.regValue .r9 = s.regValue .r9 :=
      ((ag.trans bg).trans cg).read (n := 64) (r := 9) (by simp)
    have h : t.regValue .r8 = ((c.regValue .r9).setWidth 32).setWidth 64 := te.writes
    rwa [nine] at h

end P256.Proofs.Nonce.Initialize.Prepare.Buffer
