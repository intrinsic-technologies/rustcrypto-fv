import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue (State)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reject_branch [Bindings] {initial t : RamState}
    (state : State initial t) (stack : Stack.Valid initial 656)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : t.RIP = 0x102286)
    (null : loadBytes t.external (stackPtr initial - 80) 8 = .ok (0 : BitVec 64)) :
    ∃ u, Advances (returnBoundary initial) 4 t u ∧ State initial u ∧
      u.RIP = 0x1022a9 ∧ u.regValue .rax = 1 ∧ u.external = t.external := by
  have readable : MemReadable t (stackPtr initial - 80) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 80) (len := 8)
      (by decide) (by decide)) state.allocated
  have addr : stackPtr t + 8 = stackPtr initial - 80 := by
    rw [state.rsp]
    change (stackPtr initial - 88#64) + 8#64 = stackPtr initial - 80#64
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have word : memLoad t.external (stackPtr initial - 80) 64 = 0 :=
    (P256.Proofs.Common.Memory.bytes_of_loadBytes64 readable.mem null).memLoad
      (by decide) (by decide)
  obtain ⟨a, ha, ra, ea⟩ :=
    (mov_r64_m64_effect_step 0x102286 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x2286 _
        (by decide) (by decide +kernel))
      ⟨rip, by change MemReadable t (stackPtr t + 8) 8; rw [addr]; exact readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x228b (by decide)))
  have fa : AgreesExcept [.reg 7,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have di : a.regValue .rdi = 0 := by
    have h := ea.writes
    change a.regValue .rdi = memLoad t.external (stackPtr t + 8) 64 at h
    simpa only [addr, word] using h
  obtain ⟨b, hb, rb, eb⟩ := (mov_r32_imm32_effect_step 0x10228b 0xb8 (by decide) 1).advances ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x228b _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x2290 (by decide)))
  have fb : AgreesExcept [.reg 0,.rip] a b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers])).trans ma
  have dib : b.regValue .rdi = 0 := (fb.read (n := 64) (r := 7) (by simp)).trans di
  obtain ⟨c, hc, rc, ec⟩ :=
    (test_r64_r64_effect_step 0x102290 0x48 0xff (by simp [RexWPrefix]) rfl).advances rb
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mb)
        0x2290 _ (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x2293 (by decide)))
  have fc : AgreesExcept [.flags,.rip] b c := ec.agrees
  have mc := (fc.external (by simp [Component.Covers])).trans mb
  have zfc : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = true := by
    have h := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((b.regValue .rdi &&& b.regValue .rdi) == 0) at h
    rw [dib] at h
    exact h
  have condc : condHolds 4 (StatusFlags.ofRFLAGS c.RFLAGS) = true := zfc
  have nextc : (jccEffect 0x102293 2 4 ((20 : BitVec 8).signExtend 64) c).rip = 0x1022a9 := by
    simp only [jccEffect, condc]
    decide +kernel
  obtain ⟨d, hd, rd, ed⟩ := (jcc_rel8_effect_step 0x102293 4 20).advances rc
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mc)
      0x2293 _ (by decide) (by decide +kernel)) ⟨ec.rip, by intro; decide⟩
    (by rw [nextc]; exact boundary_ne_program outside (inProgram_of_textOffset 0x22a9 (by decide)))
  have fd : AgreesExcept [.rip] c d := ed.agrees
  have frame : AgreesExcept [.reg 7,.reg 0,.flags,.rip] t d :=
    (((fa.trans fb).trans fc).trans fd).mono (by simp)
  have axFrame : AgreesExcept [.flags,.rip] b d := (fc.trans fd).mono (by simp)
  exact ⟨d, ((ha.trans hb).trans hc).trans hd,
    state.after_registers rd frame (by simp [Component.Covers]) (by simp) (by simp),
    ed.rip.trans nextc, (axFrame.read (n := 64) (r := 0) (by simp)).trans eb.writes,
    frame.external (by simp [Component.Covers])⟩

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
