import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Result.Stores
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Loop.Prefix

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_success_exit [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity : Nat} (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (pre : CalleeExitPre initial input capacity s)
    (fits : 2 * input.length ≤ capacity) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ SubroutinePost initial input capacity t := by
  have start : s.RIP = 0x1005b1 := by simpa only [fits, ↓reduceIte] using pre.rip
  obtain ⟨pointer, length, output⟩ := pre.success fits
  obtain ⟨a, run₁, state₁, rip₁, value₁, frame₁⟩ := result_store_step
    (n := 64) (address := storeAddrAt 0x1005b1 (.base 0 .none) 3)
    (offset := 24) (pc := 0x5b1) (bytes := [0x48, 0x89, 0x08])
    call pre.toMachineInvariant outside (by decide) (by decide)
    (stack_writable8 call pre.toMachineInvariant (by decide) (by decide)) start
    (by
      change (Operand.reg 0 : Operand 64).read s + (0#64) = _
      rw [BitVec.add_zero]
      exact pre.resultPointer)
    (by decide +kernel) (by decide +kernel)
    (mov_m64_r64_effect_step 0x1005b1 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.base 0 .none)
      (by unfold AddrMode.Valid; decide +kernel) rfl rfl)
  have resultPointer₁ : (Operand.reg 0 : Operand 64).read a = stackPtr initial - 24 :=
    (frame₁.read (by simp)).trans pre.resultPointer
  obtain ⟨b, run₂, state₂, rip₂, value₂, frame₂⟩ := result_store_step
    (n := 64) (address := storeAddrAt 0x1005b4 (.base 0 (.d8 8)) 4)
    (offset := 16) (pc := 0x5b4) (bytes := [0x48, 0x89, 0x78, 0x08])
    call state₁ outside (by decide) (by decide)
    (stack_writable8 call state₁ (by decide) (by decide)) rip₁
    (by
      change (Operand.reg 0 : Operand 64).read a + 8 = _
      rw [resultPointer₁]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl)
    (by decide +kernel) (by decide +kernel)
    (mov_m64_r64_effect_step 0x1005b4 0x48
      (by unfold RexWPrefix; decide +kernel) 7 (.base 0 (.d8 8))
      (by unfold AddrMode.Valid; decide +kernel) rfl rfl)
  have rsp₂ : stackPtr b = stackPtr initial - 32 :=
    ((frame₁.trans frame₂).read (r := 4) (n := 64) (by simp)).trans pre.rsp
  have inner₁ : (Operand.mem (stackPtr initial - 32) : Operand 64).read a = 0x100156 :=
    (result_store_read_mem frame₁ (stack_slots_apart call (leftOffset := 24) (leftLen := 8)
      (rightOffset := 32) (rightLen := 8) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans pre.innerReturn
  have inner₂ : (Operand.mem (stackPtr initial - 32) : Operand 64).read b = 0x100156 :=
    (result_store_read_mem frame₂ (stack_slots_apart call (leftOffset := 16) (leftLen := 8)
      (rightOffset := 32) (rightLen := 8) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans inner₁
  obtain ⟨t, run₃, state₃, rip₃, rsp₃, memory₃, rbx₃⟩ := result_ret_step
    (pc := 0x5b8) call state₂ outside rip₂ rsp₂ inner₂
      (by decide +kernel) (by decide +kernel)
  have saved : (Operand.mem (stackPtr initial - 8) : Operand 64).read t =
      initial.regValue .rbx := by
    change memLoad t.external _ 64 = _
    rw [memory₃]
    exact (result_store_read_mem frame₂ (stack_slots_apart call
      (leftOffset := 16) (leftLen := 8) (rightOffset := 8) (rightLen := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide))).trans
      ((result_store_read_mem frame₁ (stack_slots_apart call
        (leftOffset := 24) (leftLen := 8) (rightOffset := 8) (rightLen := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide))).trans pre.savedRbx)
  have lengthPointer : (Operand.reg 3 : Operand 64).read t = initial.regValue .rdx :=
    rbx₃.trans (((frame₁.trans frame₂).read (by simp)).trans pre.lengthPointer)
  refine ⟨t, run₁.trans (run₂.trans run₃), state₃, rip₃, rsp₃, ?_, saved, lengthPointer⟩
  simp only [fits, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · change memLoad t.external _ 64 = _
    rw [memory₃]
    exact (result_store_read_mem frame₂ (stack_slots_apart call (leftOffset := 16) (leftLen := 8)
      (rightOffset := 24) (rightLen := 8) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans (value₁.trans pointer)
  · change memLoad t.external _ 64 = _
    rw [memory₃]
    exact value₂.trans ((frame₁.read (r := 7) (n := 64) (by simp)).trans length)
  · have out₁ : readOutput initial a (2 * input.length) =
        readOutput initial s (2 * input.length) := by
      apply readOutput_congr_prefix
      intro j hj
      exact stack_store_output_byte_preserved call (offset := 24) (len := 8)
        (by decide) (by decide) frame₁ (by omega)
    have out₂ : readOutput initial b (2 * input.length) =
        readOutput initial a (2 * input.length) := by
      apply readOutput_congr_prefix
      intro j hj
      exact stack_store_output_byte_preserved call (offset := 16) (len := 8)
        (by decide) (by decide) frame₂ (by omega)
    unfold readOutput
    rw [memory₃]
    exact out₂.trans (out₁.trans output)

theorem callee_error_exit [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity : Nat} (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (pre : CalleeExitPre initial input capacity s)
    (fits : ¬ 2 * input.length ≤ capacity) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ SubroutinePost initial input capacity t := by
  have start : s.RIP = 0x10053c := by simpa only [fits, ↓reduceIte] using pre.rip
  obtain ⟨a, run₁, state₁, rip₁, value₁, frame₁⟩ := result_store_step
    (n := 8) (address := storeAddrAt 0x10053c (.base 0 (.d8 8)) 4)
    (offset := 16) (pc := 0x53c) (bytes := [0xc6, 0x40, 0x08, 0x01])
    call pre.toMachineInvariant outside (by decide) (by decide)
    (stack_writable1 call pre.toMachineInvariant (by decide)) start
    (by
      change (Operand.reg 0 : Operand 64).read s + 8 = _
      rw [pre.resultPointer]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl)
    (by decide +kernel) (by decide +kernel)
    (mov_m8_imm8_effect_step 0x10053c (.base 0 (.d8 8))
      (by unfold AddrMode.Valid; decide +kernel) rfl rfl 1)
  have resultPointer₁ : (Operand.reg 0 : Operand 64).read a = stackPtr initial - 24 :=
    (frame₁.read (by simp)).trans pre.resultPointer
  obtain ⟨b, run₂, state₂, rip₂, value₂, frame₂⟩ := result_store_step
    (n := 64) (address := storeAddrAt 0x100540 (.base 0 .none) 7)
    (offset := 24) (pc := 0x540) (bytes := [0x48, 0xc7, 0x00, 0, 0, 0, 0])
    call state₁ outside (by decide) (by decide)
    (stack_writable8 call state₁ (by decide) (by decide)) rip₁
    (by
      change (Operand.reg 0 : Operand 64).read a + (0#64) = _
      rw [BitVec.add_zero]
      exact resultPointer₁)
    (by decide +kernel) (by decide +kernel)
    (mov_m64_imm32_effect_step 0x100540 0x48 (by unfold RexWPrefix; decide +kernel) (.base 0 .none)
      (by unfold AddrMode.Valid; decide +kernel) rfl rfl 0)
  have rsp₂ : stackPtr b = stackPtr initial - 32 :=
    ((frame₁.trans frame₂).read (r := 4) (n := 64) (by simp)).trans pre.rsp
  have inner₁ : (Operand.mem (stackPtr initial - 32) : Operand 64).read a = 0x100156 :=
    (result_store_read_mem frame₁ (stack_slots_apart call (leftOffset := 16) (leftLen := 1)
      (rightOffset := 32) (rightLen := 8) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans pre.innerReturn
  have inner₂ : (Operand.mem (stackPtr initial - 32) : Operand 64).read b = 0x100156 :=
    (result_store_read_mem frame₂ (stack_slots_apart call (leftOffset := 24) (leftLen := 8)
      (rightOffset := 32) (rightLen := 8) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans inner₁
  obtain ⟨t, run₃, state₃, rip₃, rsp₃, memory₃, rbx₃⟩ := result_ret_step
    (pc := 0x547) call state₂ outside rip₂ rsp₂ inner₂
      (by decide +kernel) (by decide +kernel)
  have saved : (Operand.mem (stackPtr initial - 8) : Operand 64).read t =
      initial.regValue .rbx := by
    change memLoad t.external _ 64 = _
    rw [memory₃]
    exact (result_store_read_mem frame₂ (stack_slots_apart call
      (leftOffset := 24) (leftLen := 8) (rightOffset := 8) (rightLen := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide))).trans
      ((result_store_read_mem frame₁ (stack_slots_apart call
        (leftOffset := 16) (leftLen := 1) (rightOffset := 8) (rightLen := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide))).trans pre.savedRbx)
  have lengthPointer : (Operand.reg 3 : Operand 64).read t = initial.regValue .rdx :=
    rbx₃.trans (((frame₁.trans frame₂).read (by simp)).trans pre.lengthPointer)
  refine ⟨t, run₁.trans (run₂.trans run₃), state₃, rip₃, rsp₃, ?_, saved, lengthPointer⟩
  simp only [fits, ↓reduceIte]
  constructor
  · change memLoad t.external _ 64 = _
    rw [memory₃]
    exact value₂
  · change memLoad t.external _ 8 = _
    rw [memory₃]
    exact (result_store_read_mem frame₂ (stack_slots_apart call (leftOffset := 24) (leftLen := 8)
      (rightOffset := 16) (rightLen := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans value₁

theorem callee_exit [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity : Nat} (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (pre : CalleeExitPre initial input capacity s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      SubroutinePost initial input capacity t := by
  by_cases fits : 2 * input.length ≤ capacity
  · obtain ⟨t, run, post⟩ := callee_success_exit call outside pre fits
    exact ⟨3, t, run, post⟩
  · obtain ⟨t, run, post⟩ := callee_error_exit call outside pre fits
    exact ⟨3, t, run, post⟩

end Base16ct.Proofs.LowerEncode
