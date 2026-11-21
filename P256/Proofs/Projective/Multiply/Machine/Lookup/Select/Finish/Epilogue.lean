import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Finish.Memory
import P256.Proofs.Program.Copy.Return
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleeResult boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice supportedMachine_of_ready_agrees)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_return [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {select : Bool} {fuel : Nat}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : ReturnedState s t select)
    (effect : (finishCopyEffect t).Holds t u) (ready : ReadyToStep u)
    (run : Advances boundary fuel s u) :
    ∃ v, CalleeResult s v boundary 32 128 ∧
      ∀ i < 32, v.external[s.regValue .rdi + BitVec.ofNat 64 i]? = outputBytes s select i := by
  have frame := finish_copy_frame pre state.toSavedState effect
  have originalFrame : MemoryWriteFrame s u
      #v[registerRegion s .rdi 32, Stack.region s 128] := by
    intro a hout
    apply Eq.trans (frame a ?_) (state.frame a ?_)
    · intro r hr hin
      have he : r = registerRegion s .rdi 32 := by simpa using hr
      subst r
      exact hout _ (by simp) hin
    · intro r hr hin
      have he : r = Stack.region s 128 := by simpa using hr
      subst r
      exact hout _ (by simp) hin
  have loaded := Program.ScalarFrame.loaded_of_frame pre.toCalleePre originalFrame
  have code := programLoaded_codeIn loaded
  have hspu : stackPtr u = scratch s :=
    (effect.agrees.read (n := 64) (r := 4) (by simp [finishCopyEffect, Effect.components])).trans state.rsp
  have hword (off : Nat) (ho : off ≤ 128) := finish_stack_word pre frame ho
  obtain ⟨v1, ha1, hr1, he1⟩ :=
    (add_r64_imm8_effect_step 0x1143e4 0x48 0xc4 32
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready
      (programText_slice code 0x143e4 [0x48, 0x83, 0xc4, 0x20] (by decide +kernel) rfl)
      effect.rip (boundary_ne_program pre.outerBoundary
        (inProgram_of_textOffset 0x143e8 (by decide)))
  change (addR64Imm8Effect 0x1143e4 4 32 u).Holds u v1 at he1
  have hm1 : v1.external = u.external := he1.agrees.external (by simp [Component.Covers])
  have hsp1 : stackPtr v1 = stackPtr s - 8 := by
    have hw : stackPtr v1 = stackPtr u + 32 := he1.writes
    rw [hw, hspu]
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have hread1 : MemReadable v1 (stackPtr v1) 8 := by
    rw [hsp1]
    exact ((state.toSavedState.stack_readable pre (offset := 8) (len := 8)
      (by decide) (by decide)).of_holds effect).of_external_eq hm1
  obtain ⟨v2, ha2, hr2, he2⟩ :=
    (pop_r64_effect_step 0x1143e8 0x5b (by decide) (by decide)).advances hr1
      (programText_slice (code.of_external_eq hm1) 0x143e8 [0x5b] (by decide +kernel) rfl)
      ⟨he1.rip, hread1⟩ (boundary_ne_program pre.outerBoundary
        (inProgram_of_textOffset 0x143e9 (by decide)))
  change (popR64Effect 0x1143e8 1 3 v1).Holds v1 v2 at he2
  have hm2 : v2.external = u.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr v2 = stackPtr s := by
    have hw : stackPtr v2 = stackPtr v1 + 8 := he2.writes.2
    rw [hw, hsp1]
    exact BitVec.sub_add_cancel _ _
  have hbx2 : v2.regValue .rbx = s.regValue .rbx := by
    have hw : v2.regValue .rbx = (Operand.mem (stackPtr v1) : Operand 64).read v1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad v1.external (stackPtr s - 8) 64 = _
    rw [hm1]
    exact (hword 8 (by decide)).trans state.savedRbx
  have htop : stackTop v2 = (returnBoundary s).rip := by
    rw [stackTop, hsp2]
    change memLoad v2.external (stackPtr s) 64 = _
    rw [hm2]
    have hw := hword 0 (by decide)
    simp only [BitVec.sub_zero] at hw
    exact hw.trans state.returnWord
  have hread2 : MemReadable v2 (stackPtr v2) 8 := by
    rw [hsp2]
    have hw := (state.toSavedState.stack_readable pre (offset := 0) (len := 8)
      (by decide) (by decide)).of_holds effect
    simp only [BitVec.sub_zero] at hw
    exact hw.of_external_eq hm2
  obtain ⟨v3, ha3, hr3, he3⟩ := (ret_effect_step 0x1143e9).advances hr2
    (programText_slice (code.of_external_eq hm2) 0x143e9 [0xc3] (by decide +kernel) rfl)
    ⟨⟨he2.rip, hread2⟩, htop ▸ Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop v2 ≠ boundary.rip
        rw [htop]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm3 : v3.external = u.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hag := ((effect.agrees.trans he1.agrees).trans he2.agrees).trans he3.agrees
  have registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      v3.regValue r = s.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (he3.agrees.read (n := 64) (r := 3) (by simp)).trans hbx2
    all_goals apply Eq.trans _ (state.registers _ (by simp))
    all_goals first
      | exact hag.read (n := 64) (r := 5) (by simp [finishCopyEffect, addR64Imm8Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 12) (by simp [finishCopyEffect, addR64Imm8Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 13) (by simp [finishCopyEffect, addR64Imm8Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 14) (by simp [finishCopyEffect, addR64Imm8Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 15) (by simp [finishCopyEffect, addR64Imm8Effect, popR64Effect, retEffect, Effect.components])
  refine ⟨v3, {
    execution := ⟨_, ((run.trans ha1).trans ha2).trans ha3⟩
    rip := he3.rip.trans htop
    rsp := ?_
    bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported hr3 hag
    machine := supportedMachine_of_ready_agrees state.machine hr3 hag
    calleeSaved := registers
    directionFlag := hag.directionFlagClear (by component_not_mem) state.directionFlag
    mxcsr := (hag.mxcsr (by component_not_mem)).trans state.mxcsr
    fp87 := (hag.fcw (by component_not_mem)).trans state.fp87
    frame := ?_
    loaded := ?_
    allocated := fun a ha => hag.grow a (state.allocated a ha)
  }, ?_⟩
  · have hw : stackPtr v3 = stackPtr v2 + 8 := he3.writes
    change stackPtr v3 = stackPtr s + 8
    rw [hw, hsp2]
  · intro a hout
    rw [hm3]
    exact originalFrame a hout
  · intro a b hf
    rw [hm3]
    exact loaded a b hf
  · intro i hi
    rw [hm3]
    exact finish_copy_bytes pre state effect i hi

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
