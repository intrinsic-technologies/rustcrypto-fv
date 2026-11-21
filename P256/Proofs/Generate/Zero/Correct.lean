import P256.Proofs.Generate.Zero.Prefix
import P256.Proofs.Generate.Zero.Memory
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.SecretKeyFromBytes.Choice
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem zero_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x1132c0 32 32 32)
    (left : Nat256At s (s.regValue .rdi) x)
    (right : Nat256At s (s.regValue .rsi) y) :
    ∃ t, CalleeResult s t boundary 32 32 ∧
      (t.regValue .rax).setWidth 8 = (if x = y then 1 else 0) ∧
      AgreesExcept (clobbers s) s t ∧ MemoryWriteFrame s t #v[Stack.region s 32] := by
  obtain ⟨a, state⟩ := prefix_correct (offset := 0x132c0) (disp := 0x5f9d) pre
    (by constructor <;> decide +kernel) left right
  obtain ⟨b, runB, readyB, agreesB, ripB, valueB⟩ := mask_arguments boundary 0x1132d3 state.ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x132d3 maskBytes
      (by decide) (by decide +kernel)) state.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132d5 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132d8 (by decide)))
  have ab : AgreesExcept (clobbers s) s b :=
    (state.agrees.trans agreesB).mono (by simp [clobbers, prefixClobbers])
  have spB : stackPtr b = stackPtr s - 8 :=
    (agreesB.read (n := 64) (r := 4) (by simp)).trans state.rsp
  have diB : b.regValue .rdi = if x = y then 1 else 0 := by
    rw [valueB, state.value]
    split <;> rfl
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (pop_register_effect_step 0x1132d8 0 (by decide)).advances readyB
      (programText_slice (programLoaded_codeIn (loaded pre ab)) 0x132d8 (encodePopR64 0)
        (by decide) (by decide +kernel))
      ⟨ripB, by
        rw [spB]
        exact readable_of_grow
          (stack_sub_readable pre.stack (offset := 8) (len := 8) (by decide) (by decide)) ab.grow⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132d9 (by decide)))
  change (popR64Effect 0x1132d8 1 0 b).Holds b c at effectC
  have ac : AgreesExcept (clobbers s) s c :=
    (ab.trans effectC.agrees).mono (by simp [clobbers, prefixClobbers])
  have spC : stackPtr c = stackPtr s := by
    have h : stackPtr c = stackPtr b + 8 := effectC.writes.2
    rw [h, spB, BitVec.sub_add_cancel]
  obtain ⟨d, runD, readyD, effectD⟩ :=
    (jmp_rel32_effect_step 0x1132d9 0x5d92 (by decide)).advances readyC
      (programText_slice (programLoaded_codeIn (loaded pre ac)) 0x132d9 _
        (by decide) (by decide +kernel)) effectC.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19070 (by decide)))
  have ad : AgreesExcept (clobbers s) s d :=
    (ac.trans effectD.agrees).mono (by simp [clobbers, prefixClobbers])
  have spD : stackPtr d = stackPtr s :=
    (effectD.agrees.read (n := 64) (r := 4) (by simp)).trans spC
  have diD : d.regValue .rdi = if x = y then 1 else 0 :=
    ((effectC.agrees.trans effectD.agrees).read (n := 64) (r := 7) (by simp)).trans diB
  have topD : stackTop d = (returnBoundary s).rip := by
    change memLoad d.external (stackPtr d) 64 = memLoad s.external (stackPtr s) 64
    rw [spD]
    exact return_address ad
  have cp : ChoicePre d := by
    refine ⟨effectD.rip, ?_, ?_, ?_, ?_⟩
    · rw [spD]
      exact writable_of_grow (stack_sub_writable pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (offset := 1) (len := 1)
        (by decide) (by decide) (by decide)
        (by have h := Nat.mod_lt (stackPtr s - 1#64).toNat (by decide : 0 < 4096); omega)) ad.grow
    · rw [spD]
      exact readable_of_grow (by simpa only [BitVec.sub_zero] using
        (stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide))) ad.grow
    · rw [topD]
      exact inProgram_low pre.returnInProgram
    · rw [spD]
      exact P256.Proofs.HMAC.Key.stack_code_apart pre (offset := 1) (len := 1)
        (codeOffset := 0x19070) (by decide) (by decide) (by decide)
  obtain ⟨t, runT, readyT, effectT⟩ := choice_correct readyD
    (choice_code_loaded (loaded pre ad)) cp (by
      intro q hq
      apply boundary_ne_program pre.outerBoundary
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact inProgram_of_textOffset 0x19074 (by decide)
      · exact inProgram_of_textOffset 0x19078 (by decide)
      · exact inProgram_of_textOffset 0x1907c (by decide)
      · exact inProgram_of_textOffset 0x19080 (by decide)
      · rw [topD]; exact pre.returnInProgram)
  have finalAgrees : AgreesExcept (clobbers s) s t := by
    have h := effectT.agrees
    rw [spD] at h
    exact (ad.trans h).mono (by simp [clobbers, prefixClobbers])
  have frame := finalAgrees.memoryWriteFrame (writes pre)
  obtain ⟨n, runA⟩ := state.execution
  refine ⟨t, ?_, ?_, finalAgrees, frame⟩
  · refine ⟨⟨_, (((runA.trans runB).trans runC).trans runD).trans runT⟩,
      effectT.rip.trans topD, ?_,
      bindingsSupported_of_ready_agrees pre.bindingsSupported readyT finalAgrees,
      supportedMachine_of_ready_agrees pre.machine readyT finalAgrees, ?_,
      finalAgrees.directionFlagClear (by simp [clobbers, prefixClobbers]) pre.directionFlag,
      finalAgrees.mxcsr (by simp [clobbers, prefixClobbers]),
      finalAgrees.fcw (by simp [clobbers, prefixClobbers]), ?_, loaded pre finalAgrees, finalAgrees.grow⟩
    · change stackPtr t = stackPtr s + 8
      exact effectT.rsp.trans (congrArg (· + 8) spD)
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact finalAgrees.read (n := 64) (r := 3) (by simp [clobbers, prefixClobbers])
      · exact finalAgrees.read (n := 64) (r := 5) (by simp [clobbers, prefixClobbers])
      · exact finalAgrees.read (n := 64) (r := 12) (by simp [clobbers, prefixClobbers])
      · exact finalAgrees.read (n := 64) (r := 13) (by simp [clobbers, prefixClobbers])
      · exact finalAgrees.read (n := 64) (r := 14) (by simp [clobbers, prefixClobbers])
      · exact finalAgrees.read (n := 64) (r := 15) (by simp [clobbers, prefixClobbers])
    · intro address ha
      exact frame address (fun region hr hin => ha region (by simpa using Or.inr hr) hin)
  · have valueT := effectT.rax
    change t.regValue .rax = ((d.regValue .rdi).setWidth 8).setWidth 64 at valueT
    rw [valueT, diD]
    split <;> rfl

theorem correct (bindings : Bindings) : Contract bindings := by
  intro s boundary x y pre left right
  exact zero_correct pre left right

end P256.Proofs.Generate.Zero
