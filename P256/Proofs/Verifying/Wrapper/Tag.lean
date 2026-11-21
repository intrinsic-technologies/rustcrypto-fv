import P256.Proofs.Verifying.Wrapper.ReturnState
import P256.Proofs.Common.Instructions.CompareMemory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem tag_branch [Bindings] {initial t : RamState} {valid : Bool}
    (state : ReturnState initial t) (stack : Stack.Valid initial 10280)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : t.RIP = 0x1031e9)
    (tag : loadBytes t.external (stackPtr initial - 208) 8 =
      .ok (if valid then (0 : BitVec 64) else 1)) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ ReturnState initial u ∧
      u.RIP = (if valid then 0x103210 else 0x1031f0) ∧ u.external = t.external ∧
      AgreesExcept [.flags, .rip] t u := by
  have readable : MemReadable t (stackPtr initial - 208) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 208) (len := 8)
      (by decide) (by decide)) state.allocated
  have address : stackPtr initial - 280 + 72#64 = stackPtr initial - 208 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_m32_imm8_effect_step 0x1031e9 (.sib 4 none 0 (.d8 72))
      (by decide +kernel) rfl rfl 1).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x31e9 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t (stackPtr t + 72#64) 4
        rw [state.rsp, address]
        exact readable_of_grow (stack_sub_readable stack (offset := 208) (len := 4)
          (by decide) (by decide)) state.allocated⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x31ee (by decide)))
  have fa : AgreesExcept [.flags, .rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have word := P256.Proofs.Common.Memory.memLoad32_of_loadBytes64 readable.mem tag
  change memLoad t.external (stackPtr initial - 208) 32 = _ at word
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !valid := by
    have hz := cmpM32Imm8Effect_ZF (p := 0x1031e9) (len := 5)
      (am := .sib 4 none 0 (.d8 72)) (imm := 1) ea
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      decide (memLoad t.external (stackPtr t + 72#64) 32 = 1) at hz
    rw [hz, state.rsp]
    rw [address, word]
    cases valid <;> decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = valid := by
    change Bool.not (StatusFlags.ofRFLAGS a.RFLAGS).ZF = valid
    simp only [zf, Bool.not_not]
  have next : (jccEffect 0x1031ee 2 5 ((32 : BitVec 8).signExtend 64) a).rip =
      if valid then 0x103210 else 0x1031f0 := by
    simp only [jccEffect, cond]
    cases valid <;> rfl
  obtain ⟨u, hu, ru, eu⟩ := (jcc_rel8_effect_step 0x1031ee 5 32).advances ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x31ee _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; cases valid
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x31f0 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x3210 (by decide)))
  have f : AgreesExcept [.flags, .rip] t u :=
    (fa.trans eu.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])
  exact ⟨u, ha.trans hu,
    state.after_registers ru f (by simp [Component.Covers]) (by simp) (by simp),
    eu.rip.trans next, f.external (by simp [Component.Covers]), f⟩

end P256.Proofs.Verifying.Wrapper
