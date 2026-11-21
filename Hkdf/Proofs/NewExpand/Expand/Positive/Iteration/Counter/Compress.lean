import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

private def compressBytes : List UInt8 :=
  [0xba,1,0,0,0,0x48,0x8d,0xbc,0x24,0x50,1,0,0,
    0x4c,0x8d,0xb4,0x24,0x10,1,0,0,0x4c,0x89,0xf6]

private def compressEffect (s : RamState) : Effect :=
  { rip := 0x10f90a
    writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), rspOf s + 336⟩,
      ⟨(.reg 14 : Operand 64), rspOf s + 272⟩, ⟨(.reg 6 : Operand 64), rspOf s + 272⟩] }

private theorem compress_args [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f8f2)
      (codeRange 0x10f8f2 compressBytes) (Effect.post compressEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10f8f2 0xba (by decide) 1)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf8f7 (by decide))
  advance_then (lea_r64_effect_step 0x10f8f7 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f8f2 compressBytes 5 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf8ff (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f8ff 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f8f2 compressBytes 13 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf907 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f907 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f8f2 compressBytes 21 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf90a (by decide))⟩
  advance_finish [compressEffect]

private abbrev compressionLayout : StackCallLayout 2264 64 32 336 :=
  ⟨544, 264, 200, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private theorem zero_tail [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {length : Nat}
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (pc : s.RIP = 0x10f90f) :
    ∃ t, RunningFrame entry boundary length t ∧ t.RIP = 0x10f934 ∧
      t.regValue .rax = 0 ∧ AgreesExcept [.reg 0, .flags, .rip] s t := by
  obtain ⟨u, runU, readyU, zer⟩ := (xor_r32_r32_effect_step 0x10f90f 0xc0 rfl).advances
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf90f [0x31,0xc0] (by decide) (by decide +kernel))
    pc (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf911 (by decide)))
  have frameU : AgreesExcept [.reg 0, .flags, .rip] s u := zer.agrees
  have ru := no_memory ctx running runU readyU frameU (by simp [Component.Covers]) (by simp)
  obtain ⟨t, runT, readyT, jmp⟩ := (jmp_rel8_effect_step 0x10f911 0x21 (by decide)).advances readyU
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf911 [0xeb,0x21] (by decide) (by decide +kernel))
    zer.rip (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf934 (by decide)))
  have frameT : AgreesExcept [.rip] u t := jmp.agrees
  have zero : u.regValue .rax = 0 := by
    have write : u.regValue .rax =
      ((s.regValue .rax).setWidth 32 ^^^ (s.regValue .rax).setWidth 32).setWidth 64 := zer.writes
    rw [write, BitVec.xor_self]
    rfl
  exact ⟨t, no_memory ctx ru runT readyT frameT (by simp [Component.Covers]) (by simp), jmp.rip,
    (frameT.read (n := 64) (r := 0) (by simp)).trans zero, (frameU.trans frameT).mono (by simp)⟩

theorem compress [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {block : ByteArray} {hash : Array UInt32}
    (ctx : StackContext entry boundary length) (stride : UnitStringStride bindings)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f8f2)
    (words : HashStateAt s (base entry + 336) hash)
    (buffer : (⟨(base entry + 272).toNat, 64⟩ : MemoryRegion).HasBytes s.external block) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧ t.RIP = 0x10f934 ∧
      t.regValue .rax = 0 ∧ t.regValue .r14 = base entry + 272 ∧
      (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r15] : List Syntax.Reg), t.regValue r = s.regValue r) ∧
      t.MXCSR = s.MXCSR ∧ t.FP87_Control = s.FP87_Control ∧
      HashStateAt t (base entry + 336) (compressBlocks hash block) ∧
      MemoryWriteFrame s t #v[⟨(base entry + 336).toNat, 32⟩, ⟨(base entry - 344).toNat, 344⟩] := by
  obtain ⟨_, u, runU, readyU, _, args⟩ := compress_args boundary ctx.outside s
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf8f2 compressBytes
      (by decide) (by decide +kernel)) pc
  have frameU : AgreesExcept [.reg 2, .reg 7, .reg 14, .reg 6, .rip] s u := args.agrees
  have ru := no_memory ctx running runU readyU frameU (by simp [Component.Covers]) (by simp)
  have extU := frameU.external (by simp [Component.Covers])
  have spU : stackPtr u = base entry := (frameU.read (n := 64) (r := 4) (by simp)).trans sp
  have vals := args.writes
  change u.regValue .rdx = 1 ∧ u.regValue .rdi = stackPtr s + 336 ∧
    u.regValue .r14 = stackPtr s + 272 ∧ u.regValue .rsi = stackPtr s + 272 at vals
  obtain ⟨c, rc, call, ret⟩ := enter_call ctx ru spU 0xf90a 5 (by decide) args.rip
    (call_rel32_effect_step 0x10f90a 0xffff9cb1 (by decide +kernel))
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf90a (encodeCallRel32 0xffff9cb1)
      (by decide) (by decide +kernel))
    id (boundary_ne_program ctx.outside (inProgram_of_textOffset 0x95c0 (by decide)))
  have spC : stackPtr c = stackPtr entry - 544 := by
    rw [show stackPtr c = pushAddr u from call.writes.1, pushAddr, spU, base, BitVec.sub_sub]
    rfl
  have dest : c.regValue .rdi = base entry + 336 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      (vals.2.1.trans (by rw [sp]))
  have src : c.regValue .rsi = base entry + 272 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans
      (vals.2.2.2.trans (by rw [sp]))
  have dest' : c.regValue .rdi = stackPtr entry - 200 :=
    dest.trans (base_add (off := 336) (by decide))
  have callee := callee_pre_of_stack stride ctx.stack ctx.stackAvoid ctx.outside rc.machine
    rc.directionFlag rc.loaded rc.allocated compressionLayout
    (show c.RIP = 0x1095c0 from call.rip) spC (src.trans (base_add (off := 272) (by decide))) dest'
    (by rw [ret]; exact inProgram_of_textOffset 0xf90f (by decide))
  have localBytes (off width : Nat) (apart : OffsetsApart (-8) 8 (BitVec.ofNat 64 off) width)
      (small : 8 + width < 2^64) : (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees s c := by
    intro i hi
    have eq := StreamPadding.Execution.call_local_agrees call off width apart small i hi
    rw [spU, extU] at eq
    exact eq
  have p : CompressionPre c boundary hash block 1 := by
    refine ⟨callee, ?_, ?_, ?_, ?_⟩
    · rw [dest']
      change (stackPtr entry - BitVec.ofNat 64 200).toNat % 4 = 0
      rw [stack_sub_toNat ctx.stack (by decide)]
      have low := (stack_bounds ctx.stack).1
      have aligned : (stackPtr entry).toNat % 16 = 8 := ctx.stack.2.2.2
      omega
    · exact (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans vals.1
    · rw [show registerRegion c .rsi (64 * 1) = ⟨(base entry + 272).toNat, 64⟩ by simp [registerRegion, src]]
      refine ⟨buffer.1, fun i => ?_⟩
      have size : block.size = 64 := buffer.1
      have hi : i.val < 64 := by simpa only [size] using i.isLt
      have eq := localBytes 272 64 (by unfold OffsetsApart; decide +kernel) (by decide) i.val hi
      change c.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      apply eq.trans
      have byte := buffer.2 i
      change s.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _ at byte
      rwa [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    · rw [dest]
      exact hashState_of_bytes words (localBytes 336 32 (by unfold OffsetsApart; decide +kernel) (by decide))
  obtain ⟨v, result⟩ := compression_correct p
  have rv := rc.of_callee result.toCalleeResult (by
    intro r hr a ha
    exact ⟨_, by simp [regions], stack_layout_within ctx.stack compressionLayout spC dest' r hr a ha⟩)
  obtain ⟨frame, abi⟩ := call_result callee call result.toCalleeResult ru.directionFlag
  obtain ⟨t, rt, pcT, axT, frameT⟩ := zero_tail ctx rv
    (result.rip.trans (congrArg ReturnBoundary.rip ret))
  have extT := frameT.external (by simp [Component.Covers])
  have scratch : Stack.region c 336 = (⟨(base entry - 344).toNat, 344⟩ : MemoryRegion) := by
    have e : base entry - 344 = stackPtr entry - 880 := by rw [base, BitVec.sub_sub]; rfl
    have a := stack_sub_toNat ctx.stack (offset := 544) (by decide)
    have b := stack_sub_toNat ctx.stack (offset := 880) (by decide)
    have bound := (stack_bounds ctx.stack).1
    change (⟨(stackPtr c).toNat - 336,
      (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 336)⟩ : MemoryRegion) = _
    rw [e, spC]
    change (⟨(stackPtr entry - BitVec.ofNat 64 544).toNat - 336,
      (stackPtr entry - BitVec.ofNat 64 544).toNat + 8 - ((stackPtr entry - BitVec.ofNat 64 544).toNat - 336)⟩ : MemoryRegion) =
      ⟨(stackPtr entry - BitVec.ofNat 64 880).toNat, 344⟩
    rw [a, b]
    have start : (stackPtr entry).toNat - 544 - 336 = (stackPtr entry).toNat - 880 := by omega
    rw [start, show (stackPtr entry).toNat - 544 + 8 - ((stackPtr entry).toNat - 880) = 344 by omega]
  have kept (r : Syntax.Reg) (hr : r ∈ ([.rbx, .rbp, .r12, .r13, .r15] : List Syntax.Reg)) :
      t.regValue r = s.regValue r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (frameT.read (n := 64) (r := 3) (by simp)).trans
        ((abi.1 .rbx (by simp)).trans (frameU.read (n := 64) (r := 3) (by simp)))
    · exact (frameT.read (n := 64) (r := 5) (by simp)).trans
        ((abi.1 .rbp (by simp)).trans (frameU.read (n := 64) (r := 5) (by simp)))
    · exact (frameT.read (n := 64) (r := 12) (by simp)).trans
        ((abi.1 .r12 (by simp)).trans (frameU.read (n := 64) (r := 12) (by simp)))
    · exact (frameT.read (n := 64) (r := 13) (by simp)).trans
        ((abi.1 .r13 (by simp)).trans (frameU.read (n := 64) (r := 13) (by simp)))
    · exact (frameT.read (n := 64) (r := 15) (by simp)).trans
        ((abi.1 .r15 (by simp)).trans (frameU.read (n := 64) (r := 15) (by simp)))
  refine ⟨t, rt, (frameT.read (n := 64) (r := 4) (by simp)).trans
    (result.rsp.trans (congrArg ReturnBoundary.rsp ret)), pcT, axT, ?_, kept,
    (frameT.mxcsr (by simp)).trans (abi.2.2.1.trans (frameU.mxcsr (by simp))),
    (frameT.fcw (by simp)).trans (abi.2.2.2.trans (frameU.fcw (by simp))), ?_, ?_⟩
  · exact (frameT.read (n := 64) (r := 14) (by simp)).trans
      ((abi.1 .r14 (by simp)).trans (vals.2.2.1.trans (by rw [sp])))
  · apply hashState_of_bytes (show HashStateAt v (base entry + 336) _ from dest ▸ result.hashWords)
    intro i hi
    rw [extT]
  · intro a ha
    rw [extT, frame a (by simpa only [registerRegion, dest, scratch] using ha), extU]

end Hkdf.Proofs.NewExpand.Expand.Counter
