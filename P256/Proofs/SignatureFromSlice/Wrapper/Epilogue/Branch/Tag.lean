import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Common.Instructions.CompareMemory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue (State)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem tag_branch [Bindings] {initial t : RamState} {valid : Bool}
    (state : State initial t) (stack : Stack.Valid initial 656)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : t.RIP = 0x102280)
    (tag : loadBytes t.external (stackPtr initial - 88) 8 =
      .ok (if valid then (0 : BitVec 64) else 1)) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u ∧
      u.RIP = (if valid then 0x1022b1 else 0x102286) ∧ u.external = t.external := by
  have readable : MemReadable t (stackPtr initial - 88) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 88) (len := 8)
      (by decide) (by decide)) state.allocated
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_m32_imm8_effect_step 0x102280 (.sib 4 none 0 .none)
      (by decide +kernel) rfl rfl 1).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x2280 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t (stackPtr t + 0#64) 4
        rw [BitVec.add_zero, state.rsp]
        exact readable_of_grow (stack_sub_readable stack (offset := 88) (len := 4)
          (by decide) (by decide)) state.allocated⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x2284 (by decide)))
  have fa : AgreesExcept [.flags, .rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have word := P256.Proofs.Common.Memory.memLoad32_of_loadBytes64 readable.mem tag
  change memLoad t.external (stackPtr initial - 88#64) 32 = _ at word
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !valid := by
    have hz := cmpM32Imm8Effect_ZF (p := 0x102280) (len := 4)
      (am := .sib 4 none 0 .none) (imm := 1) ea
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      decide (memLoad t.external (stackPtr t + 0#64) 32 = 1) at hz
    rw [hz, BitVec.add_zero, state.rsp, word]
    cases valid <;> decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = valid := by
    change Bool.not (StatusFlags.ofRFLAGS a.RFLAGS).ZF = valid
    simp only [zf, Bool.not_not]
  have next : (jccEffect 0x102284 2 5 ((43 : BitVec 8).signExtend 64) a).rip =
      if valid then 0x1022b1 else 0x102286 := by
    simp only [jccEffect, cond]
    cases valid <;> rfl
  obtain ⟨u, hu, ru, eu⟩ := (jcc_rel8_effect_step 0x102284 5 43).advances ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x2284 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; cases valid
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x2286 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x22b1 (by decide)))
  have f : AgreesExcept [.flags, .rip] t u :=
    (fa.trans eu.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])
  exact ⟨u, ha.trans hu,
    state.after_registers ru f (by simp [Component.Covers]) (by simp) (by simp),
    eu.rip.trans next, f.external (by simp [Component.Covers])⟩

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
