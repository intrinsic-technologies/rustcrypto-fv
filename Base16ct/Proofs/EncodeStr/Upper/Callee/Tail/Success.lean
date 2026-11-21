import Base16ct.Proofs.EncodeStr.Upper.Callee.Tail.Frame
import Base16ct.Proofs.EncodeStr.Upper.Callee.Memory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem callee_success_tail [Bindings] (c : CallContext) {s : RamState}
    (hc : 2 * c.input.length ≤ c.capacity) (hs : SuccessState c s) :
    ∃ t, Advances (returnBoundary c.initial) 3 s t ∧ RunInvariant c t ∧ CalleeExit c t := by
  have ha₁ (ip : BitVec 64) : (AddrMode.base 0 .none).addr s ip =
      stackPtr c.initial - 24 := by
    change BitVec.add (s.regValue .rax) 0#64 = _
    exact (BitVec.add_zero (s.regValue .rax)).trans hs.result
  obtain ⟨s₁, hr₁, ready₁, effect₁⟩ :=
    (mov_m64_r64_effect_step 0x100641 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 0 .none)
      (by simp [AddrMode.Valid, regLow]) rfl rfl).advances (boundary := returnBoundary c.initial)
      hs.invariant.ready (program_text_slice hs.invariant.code 0x641 3 (by decide +kernel))
      ⟨hs.rip, by
        change MemWritable s ((AddrMode.base 0 .none).addr s _) 8
        rw [ha₁]
        exact hs.invariant.stack_writable c 24 (by decide) (by decide), by
        change RangeApart ((AddrMode.base 0 .none).addr s _) 8 0x100641 3
        rw [ha₁]
        exact tail_stack_code_apart c (back := 24) (offset := 0x641)
          (by decide) (by decide) (by decide +kernel)⟩
      (callee_ne_return c 0x644 (by decide +kernel))
  have frame₁ : AgreesExcept [.mem (stackPtr c.initial - 24) 8, .rip] s s₁ := by
    simpa only [movM64R64Effect_components, storeAddrAt, ha₁] using effect₁.agrees
  have invariant₁ := hs.invariant.of_callee_agrees c ready₁
    (tail_store_frame_widen c (back := 24) (by decide) (by decide) frame₁)
  have rsp₁ : stackPtr s₁ = stackPtr c.initial - 32 :=
    (frame₁.read (n := 64) (r := 4) (by simp)).trans hs.rsp
  have result₁ : s₁.regValue .rax = stackPtr c.initial - 24 :=
    (frame₁.read (n := 64) (r := 0) (by simp)).trans hs.result
  have length₁ : s₁.regValue .rdi = BitVec.ofNat 64 (2 * c.input.length) :=
    (frame₁.read (n := 64) (r := 7) (by simp)).trans hs.resultLength
  have field₁ : (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s₁ =
      c.initial.regValue .rcx := by
    have h := effect₁.writes
    change (Operand.mem ((AddrMode.base 0 .none).addr s _) : Operand 64).read s₁ =
      (Operand.reg 1 : Operand 64).read s at h
    simpa only [ha₁] using h.trans hs.dst
  have output₁ := tail_output_of_store_frame c (back := 24)
    (by decide) (by decide) hc frame₁ hs.output
  have return₁ := (calleeComponents_return c
    (tail_store_frame_widen c (back := 24) (by decide) (by decide) frame₁)).trans hs.returnAddress
  have ha₂ (ip : BitVec 64) : (AddrMode.base 0 (.d8 8)).addr s₁ ip =
      stackPtr c.initial - 16 := by
    change s₁.regValue .rax + 8 = _
    rw [result₁]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨s₂, hr₂, ready₂, effect₂⟩ :=
    (mov_m64_r64_effect_step 0x100644 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.base 0 (.d8 8))
      (by simp [AddrMode.Valid, regLow]) rfl rfl).advances (boundary := returnBoundary c.initial)
      invariant₁.ready (program_text_slice invariant₁.code 0x644 4 (by decide +kernel))
      ⟨effect₁.rip, by
        change MemWritable s₁ ((AddrMode.base 0 (.d8 8)).addr s₁ _) 8
        rw [ha₂]
        exact invariant₁.stack_writable c 16 (by decide) (by decide), by
        change RangeApart ((AddrMode.base 0 (.d8 8)).addr s₁ _) 8 0x100644 4
        rw [ha₂]
        exact tail_stack_code_apart c (back := 16) (offset := 0x644)
          (by decide) (by decide) (by decide +kernel)⟩
      (callee_ne_return c 0x648 (by decide +kernel))
  have frame₂ : AgreesExcept [.mem (stackPtr c.initial - 16) 8, .rip] s₁ s₂ := by
    simpa only [movM64R64Effect_components, storeAddrAt, ha₂] using effect₂.agrees
  have invariant₂ := invariant₁.of_callee_agrees c ready₂
    (tail_store_frame_widen c (back := 16) (by decide) (by decide) frame₂)
  have rsp₂ : stackPtr s₂ = stackPtr c.initial - 32 :=
    (frame₂.read (n := 64) (r := 4) (by simp)).trans rsp₁
  have top₂ : stackTop s₂ = 0x100476 := by
    rw [stackTop, rsp₂]
    exact (calleeComponents_return c
      (tail_store_frame_widen c (back := 16) (by decide) (by decide) frame₂)).trans return₁
  have field₂ : (Operand.mem (stackPtr c.initial - 16) : Operand 64).read s₂ =
      BitVec.ofNat 64 (2 * c.input.length) := by
    have h := effect₂.writes
    change (Operand.mem ((AddrMode.base 0 (.d8 8)).addr s₁ _) : Operand 64).read s₂ =
      (Operand.reg 7 : Operand 64).read s₁ at h
    simpa only [ha₂] using h.trans length₁
  have field₁₂ : (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s₂ =
      c.initial.regValue .rcx :=
    (tail_read_of_store_frame frame₂ (tail_stack_slots_apart _ (back := 16) (other := 24)
      (by decide) (by decide) (by decide) (by decide) (by decide))).trans field₁
  have output₂ := tail_output_of_store_frame c (back := 16)
    (by decide) (by decide) hc frame₂ output₁
  obtain ⟨t, hr₃, ready₃, effect₃⟩ := (ret_effect_step 0x100648).advances
    (boundary := returnBoundary c.initial) ready₂
    (program_text_slice invariant₂.code 0x648 1 (by decide +kernel))
    ⟨⟨effect₂.rip, by
      rw [rsp₂]
      exact invariant₂.stack_readable c 32 8 (by decide) (by decide)⟩,
      by rw [top₂]; decide⟩
    (by change stackTop s₂ ≠ _; rw [top₂]; exact callee_ne_return c 0x476 (by decide +kernel))
  have frame₃ : AgreesExcept [.reg 4, .rip] s₂ t := effect₃.agrees
  have invariant₃ := invariant₂.of_agrees c ready₃
    (frame₃.mono (by simp [encoderComponents]))
  have memory₃ := frame₃.external (by simp [Component.Covers])
  refine ⟨t, (hr₁.trans hr₂).trans hr₃, invariant₃, ?_⟩
  refine ⟨effect₃.rip.trans top₂, ?_, ?_, ?_, ?_⟩
  · have h := effect₃.writes
    change stackPtr t = stackPtr s₂ + 8 at h
    rw [h, rsp₂]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · rw [ite_eq_left hc]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Operand.read, memory₃] using field₁₂
    · simpa only [Operand.read, memory₃] using field₂
    · apply readOutput_of_bytes c
      simpa only [memory₃]
        using output₂
  · exact (((frame₁.trans frame₂).trans frame₃).read (n := 64) (r := 3) (by simp)).trans hs.rbx
  · have q := (tail_store_frame_widen c (back := 24) (by decide) (by decide) frame₁).trans
        (tail_store_frame_widen c (back := 16) (by decide) (by decide) frame₂)
    change memLoad t.external _ 64 = _
    rw [memory₃]
    exact (calleeComponents_savedRbx c (q.mono (by simp))).trans hs.savedRbx

end Base16ct.Proofs.EncodeStr.Upper
