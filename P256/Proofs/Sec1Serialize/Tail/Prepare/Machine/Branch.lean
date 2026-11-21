import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Instructions.CompareMemory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open P256.Proofs.Common.Instructions
  (cmpM32Imm8Effect cmpM32Imm8Effect_ZF cmpM32Imm8Effect_components
    cmp_m32_imm8_effect_step)

theorem prepare_uncompressed_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (rip : t.RIP = 0x11100b)
    (compress : compressionFlag s t) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧
      u.RIP = 0x111047 ∧ AgreesExcept [.flags, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 12)
  have haddr : am.addr t (0x11100b + BitVec.ofNat 64 (3 + am.tail.length)) =
      stackPtr s - 300 := by
    change stackPtr t + 12 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread : MemReadable t
      (am.addr t (0x11100b + BitVec.ofNat 64 (3 + am.tail.length))) 4 := by
    rw [haddr]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 300) (len := 4)
      (by decide) (by decide)) state.allocated
  have hc1 : CodeIn (codeRange 0x11100b (0x83 :: am.modrm 7 :: (am.tail ++ [0]))) t :=
    programText_slice (programLoaded_codeIn state.loaded) 0x1100b _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, hs1, hr1, he1⟩ := cmp_m32_imm8_effect_step 0x11100b am
    (by simp [am, AddrMode.Valid]) rfl rfl 0 t
    (readyToStep state.machine state.bindingsSupported) hc1 ⟨rip, hread⟩
  have state1 := state.after_registers hr1 he1.agrees
    (by simp [cmpM32Imm8Effect_components, Component.Covers])
    (by simp [cmpM32Imm8Effect_components])
  have hz : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = true := by
    have h := cmpM32Imm8Effect_ZF he1
    rw [haddr] at h
    change (Operand.mem (stackPtr s - 300) : Operand 32).read t = 0 at compress
    rw [compress] at h
    exact h
  have hc2 : CodeIn (codeRange 0x111010 [0x74, 0x35]) t1 :=
    programText_slice (programLoaded_codeIn state1.loaded) 0x11010 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, hs2, hr2, he2⟩ := jcc_rel8_effect_step 0x111010 4 0x35 t1 hr1 hc2
    ⟨he1.rip, by intro; decide⟩
  have next : (jccEffect 0x111010 2 4 ((0x35 : BitVec 8).signExtend 64) t1).rip =
      0x111047 := by
    simp [jccEffect, branchEffect, condHolds, hz, branchTarget]
  have state2 := state1.after_registers hr2 he2.agrees
    (by simp [jccEffect, branchEffect, Effect.components, Component.Covers])
    (by simp [jccEffect, branchEffect, Effect.components])
  have run1 : Advances boundary 1 t t1 := Advances.of_step hs1 (.inl (by
    rw [he1.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11010 (by decide))))
  have run2 : Advances boundary 1 t1 u := Advances.of_step hs2 (.inl (by
    rw [he2.rip, next]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11047 (by decide))))
  exact ⟨u, state2, ⟨2, run1.trans run2⟩, he2.rip.trans next,
    (he1.agrees.trans he2.agrees).mono (by
      simp [cmpM32Imm8Effect, jccEffect, branchEffect, Effect.components])⟩

end P256.Proofs.Sec1Serialize.Prepare
