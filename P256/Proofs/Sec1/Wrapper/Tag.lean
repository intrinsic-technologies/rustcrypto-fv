import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Common.Instructions.CompareByteMemory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CompareByteMemory

theorem tag_branch [Bindings] {initial s : RamState} {valid : Bool}
    (state : ReturnState initial s) (stack : Stack.Valid initial 4048)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x10183c)
    (tag : memLoad s.external (stackPtr initial - 232) 64 =
      if valid then 0 else 1) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ ReturnState initial t ∧
      t.RIP = (if valid then 0x10184b else 0x1018d8) ∧ t.regValue .rax = 1 ∧
      AgreesExcept [.reg 0, .flags, .rip] s t := by
  have readable : MemReadable s (stackPtr initial - 232) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 232) (len := 8)
      (by decide) (by decide)) state.allocated
  have bytes := Bytes.of_memLoad (n := 64) readable.mem
  rw [tag] at bytes
  have byte : memLoad s.external (stackPtr initial - 232) 8 =
      if valid then 0 else 1 := by
    have h := bytes.loadByte 0 (by decide)
    cases valid <;> simpa [storedByte] using h
  obtain ⟨a, ha, ra, ea⟩ := (mov_r32_imm32_effect_step 0x10183c 0xb8 (by decide) 1).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x183c _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x1841 (by decide)))
  have fa : AgreesExcept [.reg 0, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have spa : stackPtr a = stackPtr initial - 232 :=
    (fa.read (n := 64) (r := 4) (by simp)).trans state.rsp
  obtain ⟨b, hb, rb, eb⟩ := (P256.Proofs.Common.Instructions.CompareByteMemory.cmp_m8_imm8_effect_step 0x101841 (.sib 4 none 0 .none)
    (by decide) rfl rfl 0).advances ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x1841 _ (by decide) (by decide +kernel))
    ⟨ea.rip, by
      change MemReadable a (stackPtr a + 0#64) 1
      rw [BitVec.add_zero, spa]
      exact (readable_of_grow (stack_sub_readable stack (offset := 232) (len := 1)
        (by decide) (by decide)) state.allocated).of_external_eq ma⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x1845 (by decide)))
  have fb : AgreesExcept [.flags, .rip] a b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers])).trans ma
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = valid := by
    have h := cmpM8Imm8Effect_ZF eb
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      decide (memLoad a.external (stackPtr a + 0#64) 8 = 0) at h
    rw [h, BitVec.add_zero, spa, ma, byte]
    cases valid <;> decide +kernel
  have next : (jccEffect 0x101845 6 5 ((0x8d : BitVec 32).signExtend 64) b).rip =
      if valid then 0x10184b else 0x1018d8 := by
    simp only [jccEffect, condHolds, zf]
    cases valid <;> rfl
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x101845 5 0x8d).advances rb
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mb)
      0x1845 _ (by decide) (by decide +kernel)) ⟨eb.rip, by intro; decide⟩
    (by rw [next]; cases valid
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x18d8 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x184b (by decide)))
  have frame : AgreesExcept [.reg 0, .flags, .rip] s t :=
    ((fa.trans fb).trans et.agrees).mono (by simp [jccEffect])
  exact ⟨t, (ha.trans hb).trans ht,
    state.after_registers rt frame (by simp [Component.Covers]) (by simp) (by simp),
    et.rip.trans next,
    ((fb.trans et.agrees).read (n := 64) (r := 0) (by simp [jccEffect])).trans ea.writes,
    frame⟩

end P256.Proofs.Sec1.Wrapper
