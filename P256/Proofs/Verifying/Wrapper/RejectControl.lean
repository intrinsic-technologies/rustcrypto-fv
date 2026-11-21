import P256.Proofs.Verifying.Wrapper.ReturnState
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reject_branch [Bindings] {initial t : RamState}
    (state : ReturnState initial t) (stack : Stack.Valid initial 10280)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : t.RIP = 0x1031f0)
    (null : loadBytes t.external (stackPtr initial - 200) 8 = .ok (0 : BitVec 64)) :
    ∃ u, Advances (returnBoundary initial) 5 t u ∧ ReturnState initial u ∧
      u.RIP = 0x103220 ∧ u.regValue .rax = 1 ∧ u.external = t.external := by
  have readable : MemReadable t (stackPtr initial - 200) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 200) (len := 8)
      (by decide) (by decide)) state.allocated
  have addr : stackPtr t + 80 = stackPtr initial - 200 := by
    rw [state.rsp]
    change (stackPtr initial - 280#64) + 80#64 = stackPtr initial - 200#64
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have word : memLoad t.external (stackPtr initial - 200) 64 = 0 :=
    (P256.Proofs.Common.Memory.bytes_of_loadBytes64 readable.mem null).memLoad
      (by decide) (by decide)
  obtain ⟨a, ha, ra, ea⟩ :=
    (mov_r64_m64_effect_step 0x1031f0 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x31f0 _
        (by decide) (by decide +kernel))
      ⟨rip, by change MemReadable t (stackPtr t + 80) 8; rw [addr]; exact readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x31f5 (by decide)))
  have fa : AgreesExcept [.reg 7,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have di : a.regValue .rdi = 0 := by
    have h := ea.writes
    change a.regValue .rdi = memLoad t.external (stackPtr t + 80) 64 at h
    simpa only [addr, word] using h
  obtain ⟨c, hc, rc, ec⟩ :=
    (test_r64_r64_effect_step 0x1031f5 0x48 0xff (by simp [RexWPrefix]) rfl).advances ra
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
        0x31f5 _ (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x31f8 (by decide)))
  have fc : AgreesExcept [.flags,.rip] a c := ec.agrees
  have mc := (fc.external (by simp [Component.Covers])).trans ma
  have zfc : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = true := by
    have h := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((a.regValue .rdi &&& a.regValue .rdi) == 0) at h
    rw [di] at h
    exact h
  have condc : condHolds 4 (StatusFlags.ofRFLAGS c.RFLAGS) = true := zfc
  have nextc : (jccEffect 0x1031f8 2 4 ((15 : BitVec 8).signExtend 64) c).rip = 0x103209 := by
    simp only [jccEffect, condc]
    decide +kernel
  obtain ⟨d, hd, rd, ed⟩ := (jcc_rel8_effect_step 0x1031f8 4 15).advances rc
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mc)
      0x31f8 _ (by decide) (by decide +kernel)) ⟨ec.rip, by intro; decide⟩
    (by rw [nextc]; exact boundary_ne_program outside (inProgram_of_textOffset 0x3209 (by decide)))
  have fd : AgreesExcept [.rip] c d := ed.agrees
  have md := (fd.external (by simp [Component.Covers])).trans mc
  obtain ⟨e, he, re, ee⟩ := (mov_r32_imm32_effect_step 0x103209 0xb8 (by decide) 1).advances rd
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq md)
      0x3209 _ (by decide) (by decide +kernel)) (ed.rip.trans nextc)
    (boundary_ne_program outside (inProgram_of_textOffset 0x320e (by decide)))
  have fe : AgreesExcept [.reg 0, .rip] d e := ee.agrees
  have me := (fe.external (by simp [Component.Covers])).trans md
  obtain ⟨u, hu, ru, eu⟩ := (jmp_rel8_effect_step 0x10320e 0x10 (by decide)).advances re
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq me)
      0x320e _ (by decide) (by decide +kernel)) ee.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x3220 (by decide)))
  have fu : AgreesExcept [.rip] e u := eu.agrees
  have frame : AgreesExcept [.reg 7, .reg 0, .flags, .rip] t u :=
    ((((fa.trans fc).trans fd).trans fe).trans fu).mono (by simp)
  exact ⟨u, (((ha.trans hc).trans hd).trans he).trans hu,
    state.after_registers ru frame (by simp [Component.Covers]) (by simp) (by simp),
    eu.rip, (fu.read (n := 64) (r := 0) (by simp)).trans ee.writes,
    frame.external (by simp [Component.Covers])⟩

end P256.Proofs.Verifying.Wrapper
