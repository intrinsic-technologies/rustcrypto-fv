import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Store
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

private def fillBytes : List UInt8 :=
  [0xba,0x40,0,0,0,0x48,0x29,0xc2,0x48,0x8d,0x3c,0x04,0x48,0x81,0xc7,0x10,1,0,0,
    0x4c,0x89,0xfe,0x4c,0x89,0xe3]

private def fillEffect (s : RamState) : Effect :=
  { rip := 0x10f8e7
    writes := [⟨(.reg 2 : Operand 64), 64 - (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 72)) (modrmReg 194)) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg 0 : Operand 64).read s + 272⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 76)) (modrmReg 254)) : Operand 64).read s⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 76)) (modrmReg 227)) : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s + (Operand.reg 0 : Operand 64).read s) (272 : BitVec 64)).2) }

set_option maxHeartbeats 550000 in
private theorem fill_args [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f8ce)
      (codeRange 0x10f8ce fillBytes) (Effect.post fillEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10f8ce 0xba (by decide) 64)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf8d3 (by decide))
  advance_then (sub_r64_r64_effect_step 0x10f8d3 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f8ce fillBytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8d6 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f8d6 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 (some 0) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f8ce fillBytes 8 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8da (by decide))⟩
  advance_then (add_r64_imm32_effect_step 0x10f8da 0x48 0xc7 272 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f8ce fillBytes 12 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8e1 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f8e1 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f8ce fillBytes 19 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8e4 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f8e4 0x4c 0xe3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f8ce fillBytes 22 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8e7 (by decide))⟩
  advance_finish [fillEffect, BitVec.shiftLeft_zero, BitVec.add_zero]

private abbrev fillLayout : StackCallLayout 2264 1 1 0 :=
  ⟨544, 456, 201, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem copy_byte [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {b : UInt8} (ctx : StackContext entry boundary length) (stride : UnitStringStride bindings)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f8ce) (ax : s.regValue .rax = 63)
    (r12 : s.regValue .r12 = 0x10dd60) (r15 : s.regValue .r15 = base entry + 80)
    (byte : s.external[base entry + 80]? = some b) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧ t.RIP = 0x10f8ea ∧
      t.regValue .rbx = 0x10dd60 ∧ t.regValue .r12 = s.regValue .r12 ∧
      t.regValue .r13 = s.regValue .r13 ∧ t.regValue .r15 = s.regValue .r15 ∧
      t.regValue .rbp = s.regValue .rbp ∧ t.MXCSR = s.MXCSR ∧ t.FP87_Control = s.FP87_Control ∧
      t.external[base entry + 335]? = some b ∧
      MemoryWriteFrame s t #v[⟨(base entry + 335).toNat, 1⟩, ⟨(base entry - 8).toNat, 8⟩] := by
  obtain ⟨_, u, runU, readyU, _, args⟩ := fill_args boundary ctx.outside s
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf8ce fillBytes (by decide) (by decide +kernel)) pc
  have frameU : AgreesExcept [.reg 2, .reg 7, .reg 6, .reg 3, .flags, .rip] s u := args.agrees
  have noMem : ∀ c ∈ ([.reg 2, .reg 7, .reg 6, .reg 3, .flags, .rip] : List Component), ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  have ru := no_memory ctx running runU readyU frameU noMem (by simp)
  have spU : stackPtr u = base entry := (frameU.read (n := 64) (r := 4) (by simp)).trans sp
  have vals := args.writes
  change u.regValue .rdx = 64 - s.regValue .rax ∧
    u.regValue .rdi = stackPtr s + s.regValue .rax + 272 ∧
    u.regValue .rsi = s.regValue .r15 ∧ u.regValue .rbx = s.regValue .r12 at vals
  have target : (Operand.reg 12 : Operand 64).read u = 0x10dd60 :=
    (frameU.read (n := 64) (r := 12) (by simp)).trans r12
  obtain ⟨c, rc, call, ret⟩ := enter_call ctx ru spU 0xf8e7 3 (by decide) args.rip
    (call_r64_rex_effect_step 0x10f8e7 0x41 0xd4 (by simp [RexPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf8e7 [0x41,0xff,0xd4] (by decide) (by decide +kernel))
    (fun pushed => ⟨pushed, by
      change ((Operand.reg 12 : Operand 64).read u).toNat < 2^32
      rw [target]; decide⟩)
    (by change (Operand.reg 12 : Operand 64).read u ≠ _; rw [target]
        exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xdd60 (by decide)))
  have spC : stackPtr c = stackPtr entry - 544 := by
    rw [show stackPtr c = pushAddr u from call.writes.1, pushAddr, spU, base, BitVec.sub_sub]
    rfl
  have src : c.regValue .rsi = base entry + 80 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans (vals.2.2.1.trans r15)
  have dest : c.regValue .rdi = base entry + 335 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      (by change u.regValue .rdi = _; rw [vals.2.1, sp, ax]; bv_omega)
  have len : c.regValue .rdx = 1 :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans
      (by change u.regValue .rdx = _; rw [vals.1, ax]; decide)
  have dest' : c.regValue .rdi = stackPtr entry - 201 :=
    dest.trans (base_add (off := 335) (by decide))
  have callee := callee_pre_of_stack stride ctx.stack ctx.stackAvoid ctx.outside rc.machine
    rc.directionFlag rc.loaded rc.allocated fillLayout (call.rip.trans target) spC
    (src.trans (base_add (off := 80) (by decide))) dest'
    (by rw [ret]; exact inProgram_of_textOffset 0xf8ea (by decide))
  obtain ⟨t, result, copied, _⟩ := Memory.memcpy_correct callee len (by decide)
  obtain ⟨frame, abi⟩ := call_result callee call result ru.directionFlag
  have runningT := rc.of_callee result (by
    intro r hr a ha
    exact ⟨_, by simp [regions], stack_layout_within ctx.stack fillLayout spC dest' r hr a ha⟩)
  have scratch : Stack.region c 0 = (⟨(base entry - 8).toNat, 8⟩ : MemoryRegion) := by
    have e : stackPtr c = base entry - 8 := by rw [spC, base, BitVec.sub_sub]; rfl
    change (⟨(stackPtr c).toNat - 0, (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 0)⟩ : MemoryRegion) = _
    rw [e]
    congr 1 <;> omega
  have byteC : c.external[base entry + 80]? = some b := by
    have same := StreamPadding.Execution.call_local_agrees call 80 1
      (by unfold OffsetsApart; decide +kernel) (by decide) 0 (by decide)
    simp only [BitVec.add_zero] at same
    rw [spU, frameU.external noMem] at same
    exact same.trans byte
  have byteT : t.external[base entry + 335]? = some b := by
    have h := copied 0 (by decide)
    simp only [src, dest, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h
    exact h.trans byteC
  exact ⟨t, runningT, result.rsp.trans (congrArg ReturnBoundary.rsp ret),
    result.rip.trans (congrArg ReturnBoundary.rip ret),
    (abi.1 .rbx (by simp)).trans (vals.2.2.2.trans r12),
    (abi.1 .r12 (by simp)).trans (frameU.read (n := 64) (r := 12) (by simp)),
    (abi.1 .r13 (by simp)).trans (frameU.read (n := 64) (r := 13) (by simp)),
    (abi.1 .r15 (by simp)).trans (frameU.read (n := 64) (r := 15) (by simp)),
    (abi.1 .rbp (by simp)).trans (frameU.read (n := 64) (r := 5) (by simp)),
    abi.2.2.1.trans (frameU.mxcsr (by simp)), abi.2.2.2.trans (frameU.fcw (by simp)), byteT,
    memoryWriteFrame_trans (by intro a _; rw [frameU.external noMem])
      (by simpa only [registerRegion, dest, scratch] using frame)⟩

theorem increment_blocks [Bindings] {entry s : RamState} {length : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f8ea) :
    ∃ t, RunningFrame entry boundary length t ∧ ReadyToStep t ∧ stackPtr t = base entry ∧
      t.RIP = 0x10f8f2 ∧ memLoad t.external (base entry + 368) 64 = slot s 368 + 1 ∧
      AgreesExcept [.mem (base entry + 368) 8, .flags, .rip] s t := by
  have writable : MemWritable s (base entry + 368) 8 := by
    rw [show base entry + 368 = stackPtr entry - 168 from base_add (off := 368) (by decide)]
    exact stack_writable8 ctx.stack ctx.stackAvoid running.allocated (by decide) (by decide)
  obtain ⟨t, run, ready, inc⟩ := (inc_m64_effect_step 0x10f8ea 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl).advances
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf8ea [0x48,0xff,0x84,0x24,0x70,1,0,0]
      (by decide) (by decide +kernel))
    ⟨pc, by change MemWritable s (stackPtr s + 368) 8; rwa [sp],
      by change RangeApart (stackPtr s + 368) 8 0x10f8ea 8; rw [sp]
         exact stack_apart ctx (off := 368) (codeOff := 0xf8ea) (by decide) (by decide) (by decide)⟩
    (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf8f2 (by decide)))
  have frame : AgreesExcept [.mem (base entry + 368) 8, .flags, .rip] s t := by
    have h : AgreesExcept [.mem (stackPtr s + 368) 8, .flags, .rip] s t := by
      have h := inc.agrees
      rw [incMEffect_components] at h
      exact h
    rwa [sp] at h
  have writes : WritesWithin [.mem (base entry + 368) 8, .flags, .rip] (regions entry length) := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact stack_writes ctx (off := 368) (size := 8) (by decide) (by decide) _ (by simp) a ha
    · exact ha.elim
    · exact ha.elim
  have stored : memLoad t.external (stackPtr s + 368) 64 = slot s 368 + 1 := inc.writes
  exact ⟨t, running.of_agrees run ready frame writes ctx.avoids (by simp), ready,
    (frame.read (n := 64) (r := 4) (by simp)).trans sp, inc.rip, by rwa [sp] at stored, frame⟩

end Hkdf.Proofs.NewExpand.Expand.Counter
