import P256.Proofs.Verifying.Core.Finish.Tail.EqualChoice
import P256.Proofs.Common.Field.Operations.Select.TestAl
import P256.Proofs.Common.Instructions.OrLoad.Setne
import X86Proofs.Instructions.Pop.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Generate.Zero (prefixClobbers)
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem scalar_equal_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x1132e0 32 32 32)
    (left : Nat256At s (s.regValue .rdi) x)
    (right : Nat256At s (s.regValue .rsi) y) :
    ∃ t, CalleeResult s t boundary 32 32 ∧
      (t.regValue .rax).setWidth 8 = if x = y then 1 else 0 := by
  obtain ⟨a, ⟨n, runA⟩, readyA, agA, ripA, spA, valueA⟩ := choice pre left right
  obtain ⟨b, runB, readyB, effectB⟩ := (test_al_al_effect_step 0x1132fd).advances readyA
    (programText_slice (programLoaded_codeIn (loaded pre agA)) 0x132fd _
      (by decide) (by decide +kernel)) ripA
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132ff (by decide)))
  have agB : AgreesExcept (clobbers s) s b :=
    (agA.trans effectB.agrees).mono (by simp [clobbers, prefixClobbers, testAlEffect, Effect.components])
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = if x = y then false else true := by
    have hz := effectB.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = ((a.regValue .rax).setWidth 8 == 0) at hz
    rw [hz, valueA]
    split <;> rfl
  obtain ⟨c, runC, readyC, effectC⟩ := (setne_r8_effect_step 0x1132ff 0xc0 rfl (by decide)).advances readyB
    (programText_slice (programLoaded_codeIn (loaded pre agB)) 0x132ff _
      (by decide) (by decide +kernel)) effectB.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13302 (by decide)))
  change (P256.Proofs.Common.Instructions.Setb.setccR8Effect 0x1132ff 3 0 5 b).Holds b c at effectC
  have agC : AgreesExcept (clobbers s) s c :=
    (agB.trans effectC.agrees).mono (by simp [clobbers, prefixClobbers, P256.Proofs.Common.Instructions.Setb.setccR8Effect_components])
  have valueC : (c.regValue .rax).setWidth 8 = if x = y then 1 else 0 := by
    have hc := effectC.writes
    change c.regValue .rax = mergeGPR 8 (P256.Proofs.Common.Instructions.Setb.setccValue 5 b) b.GPR[gprIndex 0] at hc
    rw [hc, mergeGPR_low8]
    change (if !(StatusFlags.ofRFLAGS b.RFLAGS).ZF then 1 else 0) = _
    rw [zf]
    split <;> rfl
  have spC : stackPtr c = stackPtr s - 8 :=
    ((effectB.agrees.trans effectC.agrees).read (n := 64) (r := 4)
      (by simp [testAlEffect, P256.Proofs.Common.Instructions.Setb.setccR8Effect, Effect.components])).trans spA
  obtain ⟨d, runD, readyD, effectD⟩ :=
    (pop_r64_effect_step 0x113302 0x59 (by decide) (by decide)).advances readyC
      (programText_slice (programLoaded_codeIn (loaded pre agC)) 0x13302 [0x59]
        (by decide) (by decide +kernel))
      ⟨effectC.rip, by
        rw [spC]
        exact readable_of_grow (stack_sub_readable pre.stack
          (offset := 8) (len := 8) (by decide) (by decide)) agC.grow⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13303 (by decide)))
  change (popR64Effect 0x113302 1 1 c).Holds c d at effectD
  have agD : AgreesExcept (clobbers s) s d :=
    (agC.trans effectD.agrees).mono (by simp [clobbers, prefixClobbers])
  have spD : stackPtr d = stackPtr s := by
    have eq : stackPtr d = stackPtr c + 8 := effectD.writes.2
    rw [eq, spC, BitVec.sub_add_cancel]
  have topD : stackTop d = (returnBoundary s).rip := by
    change memLoad d.external (stackPtr d) 64 = memLoad s.external (stackPtr s) 64
    rw [spD]
    exact return_address agD
  have retPre : RetPre 0x113303 d := by
    refine ⟨⟨effectD.rip, ?_⟩, ?_⟩
    · rw [spD]
      exact readable_of_grow
        (by simpa only [BitVec.sub_zero] using (stack_sub_readable pre.stack
          (offset := 0) (len := 8) (by decide) (by decide))) agD.grow
    · rw [topD]
      exact inProgram_low pre.returnInProgram
  obtain ⟨t, runT, readyT, effectT⟩ := (ret_effect_step 0x113303).advances readyD
    (programText_slice (programLoaded_codeIn (loaded pre agD)) 0x13303 [0xc3]
      (by decide) (by decide +kernel)) retPre (by
      change stackTop d ≠ boundary.rip
      rw [topD]
      exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have agT : AgreesExcept (clobbers s) s t :=
    (agD.trans effectT.agrees).mono (by simp [clobbers, prefixClobbers])
  refine ⟨t, ⟨⟨_,((((runA.trans runB).trans runC).trans runD).trans runT)⟩,
    effectT.rip.trans topD, ?_,
    bindingsSupported_of_ready_agrees pre.bindingsSupported readyT agT,
    supportedMachine_of_ready_agrees pre.machine readyT agT, ?_,
    agT.directionFlagClear (by simp [clobbers,prefixClobbers]) pre.directionFlag,
    agT.mxcsr (by simp [clobbers,prefixClobbers]),
    agT.fcw (by simp [clobbers,prefixClobbers]), ?_, loaded pre agT, agT.grow⟩, ?_⟩
  · change stackPtr t = stackPtr s + 8
    have eq : stackPtr t = stackPtr d + 8 := effectT.writes
    rw [eq, spD]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact agT.read (n := 64) (r := 3) (by simp [clobbers, prefixClobbers])
    · exact agT.read (n := 64) (r := 5) (by simp [clobbers, prefixClobbers])
    · exact agT.read (n := 64) (r := 12) (by simp [clobbers, prefixClobbers])
    · exact agT.read (n := 64) (r := 13) (by simp [clobbers, prefixClobbers])
    · exact agT.read (n := 64) (r := 14) (by simp [clobbers, prefixClobbers])
    · exact agT.read (n := 64) (r := 15) (by simp [clobbers, prefixClobbers])
  · apply agT.memoryWriteFrame
    intro c hc a ha
    obtain ⟨region, hr, hin⟩ := writes pre c hc a ha
    have eq : region = Stack.region s 32 := by simpa using hr
    subst region
    exact ⟨Stack.region s 32, by simp, hin⟩
  · have valueT : t.regValue .rax = c.regValue .rax :=
      (effectD.agrees.trans effectT.agrees).read (n := 64) (r := 0)
        (by simp [popR64Effect, retEffect, Effect.components])
    rw [valueT]
    exact valueC

end P256.Proofs.Verifying.Core.Finish.Tail.Equal
