import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Key.Tail.Epilogue
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def restoreBytes : List UInt8 :=
  [0x48, 0x89, 0xd8, 0x48, 0x81, 0xc4, 0x98, 0x01, 0, 0,
    0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3]

private structure RestorePre (s : RamState) : Prop where
  rip : s.RIP = 0x10fcf6
  readable : ∀ i < 7, MemReadable s (rspOf s + BitVec.ofNat 64 (408 + 8 * i)) 8
  returnInProgram : InProgram (memLoad s.external (rspOf s + 456) 64)

private def restoreEffect (s : RamState) : Effect where
  rip := memLoad s.external (rspOf s + 456) 64
  writes := [
    ⟨(.reg 0 : Operand 64), rbx.read s⟩,
    ⟨(.reg 4 : Operand 64), rspOf s + 464⟩,
    ⟨(.reg 3 : Operand 64), memLoad s.external (rspOf s + 408) 64⟩,
    ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + 416) 64⟩,
    ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 424) 64⟩,
    ⟨(.reg 14 : Operand 64), memLoad s.external (rspOf s + 432) 64⟩,
    ⟨(.reg 15 : Operand 64), memLoad s.external (rspOf s + 440) 64⟩,
    ⟨(.reg 5 : Operand 64), memLoad s.external (rspOf s + 448) 64⟩]
  flags := some (.ofStatusFlags (addSpec (rspOf s) (408 : BitVec 64)).2)

local macro "restore_pop_pre " slot:term "," next:term : tactic => `(tactic| (
  intro s t hP hH hO
  refine ⟨⟨hH.rip_of (by x86_norm),
    MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
  · x86_norm
    exact hP.readable $slot (by decide)
  · apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  · apply boundary_ne_program (by assumption)
    exact inProgram_of_textOffset $next (by decide)))

private theorem restore_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary RestorePre (codeRange 0x10fcf6 restoreBytes)
      (Effect.post restoreEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10fcf6 0x48 0xd8 (by simp [RexWPrefix]) rfl)
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xfcf9 (by decide))
  advance_then (show StepEffect _ _ (addR64Imm32Effect 0x10fcf9 4 408) from
    add_r64_imm32_effect_step 0x10fcf9 0x48 0xc4 408 (by simp [RexWPrefix])
      (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 3 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfd00 (by decide))⟩
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd00 3 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 10 1
  case mid => restore_pop_pre 0, 0xfd01
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd01 12 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 11 2
  case mid => restore_pop_pre 1, 0xfd03
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd03 13 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 13 2
  case mid => restore_pop_pre 2, 0xfd05
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd05 14 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 15 2
  case mid => restore_pop_pre 3, 0xfd07
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd07 15 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 17 2
  case mid => restore_pop_pre 4, 0xfd09
  advance_then (Encoding.Serialize.pop_register_effect_step 0x10fd09 5 (by decide))
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 19 1
  case mid => restore_pop_pre 5, 0xfd0a
  advance_then (ret_effect_step 0x10fd0a)
  case sub => exact codeRange_slice_subset 0x10fcf6 restoreBytes 20 1
  case mid =>
    intro s t hP hH hO
    have top : stackTop t = memLoad s.external (rspOf s + 456) 64 := by
      rw [← Hkdf.Proofs.Key.Tail.Epilogue.stackTop_obs (hO true)]
      x86_norm
    refine ⟨⟨⟨hH.rip_of (by x86_norm),
      MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 6 (by decide)
    · rw [top]
      obtain ⟨byte, hb⟩ := hP.returnInProgram
      exact programSections_low.codeLow _ hb
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change stackTop t ≠ boundary.rip
      rw [top]
      exact boundary_ne_program outside hP.returnInProgram
  advance_finish [restoreEffect]

theorem restore [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (running : CallFrame.Running initial boundary
      #v[registerRegion initial .rdi 176, Stack.region initial 2264] s)
    (saved : Saved initial s) (rip : s.RIP = 0x10fcf6) (rsp : stackPtr s = base initial) :
    ∃ t, CalleeResult initial t boundary 176 2264 ∧ t.external = s.external := by
  have sp : rspOf s = stackPtr initial - 456 := rsp
  have returnWord : memLoad s.external (rspOf s + 456) 64 = (returnBoundary initial).rip := by
    rw [sp, BitVec.sub_add_cancel]
    exact saved.returnAddress.symm
  have slotAddress {slot offset : Nat} (sum : slot + offset = 456) :
      rspOf s + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 slot := by
    have stop : (456 : BitVec 64) = BitVec.ofNat 64 slot + BitVec.ofNat 64 offset := by
      rw [← BitVec.ofNat_add, sum]
      rfl
    rw [sp, stop, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have readable (i : Nat) (hi : i < 7) :
      MemReadable s (rspOf s + BitVec.ofNat 64 (408 + 8 * i)) 8 := by
    have ho : 408 + 8 * i ≤ 456 := by omega
    rw [slotAddress (Nat.sub_add_cancel ho)]
    exact CallFrame.stack_readable pre.call.stack running.allocated (by omega) (by omega)
  obtain ⟨fuel, t, execution, ready, _, effect⟩ :=
    restore_run boundary pre.call.outerBoundary s (supportedMachine_readyToStep running.machine)
      (programText_slice (programLoaded_codeIn running.loaded) 0xfcf6 restoreBytes
        (by decide +kernel) (by decide +kernel))
      ⟨rip, readable, returnWord ▸ pre.call.returnInProgram⟩
  have noMemory : ∀ c ∈ (restoreEffect s).components, ∀ a, ¬ c.Covers a := by
    simp [restoreEffect, Effect.components, Component.Covers]
  have final := running.of_agrees execution ready effect.agrees
    (by intro c hc a ha; exact (noMemory c hc a ha).elim)
    (by
      intro region member address contains inProgram
      have hr : region ∈ [registerRegion initial .rdi 176, Stack.region initial 2264] := by
        simpa using member
      rcases List.mem_cons.mp hr with rfl | hStack
      · exact pre.call.writesAvoid _ (by simp) address contains (.inl inProgram)
      · have eq : region = Stack.region initial 2264 := by simpa using hStack
        exact pre.call.stackAvoid address (eq ▸ contains) (.inl inProgram))
    (by simp [restoreEffect, Effect.components])
  have restored := effect.writes
  simp only [restoreEffect, Write.AllHold] at restored
  have restoredRegister {slot : Syntax.Reg × Nat}
      (member : slot ∈ Encoding.Serialize.savedRegisters) {offset : Nat}
      (sum : slot.2 + offset = 456)
      (value : t.regValue slot.1 = memLoad s.external (rspOf s + BitVec.ofNat 64 offset) 64) :
      t.regValue slot.1 = initial.regValue slot.1 := by
    rw [value, slotAddress sum]
    exact saved.registers slot member
  have restoredRsp : t.regValue .rsp = (returnBoundary initial).rsp := by
    change rspOf t = stackPtr initial + 8
    rw [show rspOf t = rspOf s + 464 from restored.2.1, sp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    rfl
  refine ⟨t, {
    execution := final.execution
    rip := effect.rip.trans returnWord
    rsp := restoredRsp
    machine := final.machine
    abi := ⟨?_, final.directionFlag, ?_, ?_⟩
    frame := final.frame
    loaded := final.loaded
    allocated := final.allocated
  }, effect.agrees.external noMemory⟩
  · intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact restoredRegister (slot := (.rbx, 48)) (offset := 408)
        (by decide) rfl restored.2.2.1
    · exact restoredRegister (slot := (.rbp, 8)) (offset := 448)
        (by decide) rfl restored.2.2.2.2.2.2.2
    · exact restoredRegister (slot := (.r12, 40)) (offset := 416)
        (by decide) rfl restored.2.2.2.1
    · exact restoredRegister (slot := (.r13, 32)) (offset := 424)
        (by decide) rfl restored.2.2.2.2.1
    · exact restoredRegister (slot := (.r14, 24)) (offset := 432)
        (by decide) rfl restored.2.2.2.2.2.1
    · exact restoredRegister (slot := (.r15, 16)) (offset := 440)
        (by decide) rfl restored.2.2.2.2.2.2.1
  · exact (effect.agrees.mxcsr (by simp [restoreEffect, Effect.components])).trans saved.mxcsr
  · exact (effect.agrees.fcw (by simp [restoreEffect, Effect.components])).trans saved.fcw

end Hkdf.Proofs.NewExpand.Extract
