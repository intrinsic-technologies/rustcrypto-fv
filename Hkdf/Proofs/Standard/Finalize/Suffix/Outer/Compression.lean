import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Compression

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.StreamPadding (base regions writes)
open Hkdf.Proofs.Common.StreamPadding.Execution
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

private abbrev layout : StackCallLayout 1264 64 32 336 :=
  ⟨416, 400, 232, by decide, by decide, by decide, by decide, by decide,
    by decide, .inl (by decide)⟩

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {block : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s)
    (rip : s.RIP = 0x10e01b)
    (destination : s.regValue .rdi = stackPtr initial - 232)
    (source : s.regValue .rsi = stackPtr initial - 400)
    (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr initial - 400).toNat, 64⟩ : MemoryRegion).HasBytes s.external block)
    (words : HashStateAt s (stackPtr initial - 232) hash) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e020 ∧
      HashStateAt t (stackPtr initial - 232)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  have rsp : stackPtr s = base .hmac initial := state.rsp
  have step := call_rel32_effect_step 0x10e01b 0xffffb5a0 (by decide +kernel)
  have instruction : CodeIn (codeRange 0x10e01b (encodeCallRel32 0xffffb5a0)) s :=
    programText_slice (programLoaded_codeIn state.running.loaded) 0xe01b _
      (by decide) (by decide +kernel)
  have conditions : PushPre 0x10e01b 5 s :=
    ⟨rip, call_writable .hmac pre state.running rsp,
      call_codeApart .hmac pre rsp 0xe01b 5 (by decide)⟩
  have target : branchTarget 0x10e01b 5 ((0xffffb5a0 : BitVec 32).signExtend 64) =
      0x1095c0 := by decide +kernel
  obtain ⟨c, runningC, called, returnC⟩ := state.running.call step instruction conditions
    (by
      rw [target]
      exact boundary_ne_program pre.outerBoundary
        (inProgram_of_textOffset 0x95c0 (by decide)))
    (by
      intro component member a covered
      obtain ⟨region, hr, contains⟩ := call_writes .hmac pre rsp
        (fun _ => branchTarget 0x10e01b 5 ((0xffffb5a0 : BitVec 32).signExtend 64))
        0x10e020 component member a covered
      exact writes_within_regions .hmac pre region hr a.toNat contains)
    (regions_avoids .hmac pre)
  have rspC : stackPtr c = stackPtr initial - 416 := by
    exact called.writes.1.trans (by change stackPtr s - 8 = _; rw [state.rsp]; bv_omega)
  have outputC : c.regValue .rdi = stackPtr initial - 232 :=
    (called.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans destination
  have inputC : c.regValue .rsi = stackPtr initial - 400 :=
    (called.agrees.read (n := 64) (r := 6)
      (by simp [callEffect, pushEffect_components])).trans source
  have countC : c.regValue .rdx = 1 :=
    (called.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans count
  have callee : CalleePre c boundary 0x1095c0 64 32 336 := by
    apply callee_pre_of_stack pre.stride pre.stack (pre.avoids _ (by simp))
      pre.outerBoundary runningC.machine runningC.directionFlag runningC.loaded
      runningC.allocated layout (called.rip.trans target) rspC inputC outputC
    rw [returnC]
    exact inProgram_of_textOffset 0xe020 (by decide)
  have hashSame : (Component.mem (stackPtr initial - 232) 32).Agrees s c := by
    have same := call_local_agrees called 176 32
      (by unfold OffsetsApart; decide +kernel) (by decide)
    rw [show stackPtr s + BitVec.ofNat 64 176 = stackPtr initial - 232 by
      rw [state.rsp]; bv_omega] at same
    exact same
  have scratchSame : (Component.mem (stackPtr initial - 400) 64).Agrees s c := by
    have same := call_local_agrees called 8 64
      (by unfold OffsetsApart; decide +kernel) (by decide)
    rw [show stackPtr s + BitVec.ofNat 64 8 = stackPtr initial - 400 by
      rw [state.rsp]; bv_omega] at same
    exact same
  have hashC : HashStateAt c (c.regValue .rdi) hash := by
    rw [outputC]
    exact Hkdf.Proofs.Common.hashState_of_bytes words hashSame
  have bytesC : (registerRegion c .rsi 64).HasBytes c.external block := by
    change (⟨(c.regValue .rsi).toNat, 64⟩ : MemoryRegion).HasBytes _ _
    rw [inputC]
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 64 := by have h := i.isLt; have size : block.size = 64 := bytes.1; omega
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (scratchSame i.val hi).trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 i)
  have compression : Hkdf.Proofs.Common.SHA256.CompressionPre c boundary hash block 1 := by
    refine ⟨callee, ?_, countC, bytesC, hashC⟩
    rw [outputC, show (stackPtr initial - 232).toNat = (stackPtr initial).toNat - 232 from
      stack_sub_toNat pre.stack (by decide : 232 ≤ 1264)]
    have aligned : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
    have bounds := stack_bounds pre.stack
    omega
  obtain ⟨t, result⟩ := Hkdf.Proofs.Common.SHA256.compression_correct compression
  have runningT := runningC.of_callee result.toCalleeResult (by
    intro region member a contains
    exact ⟨Stack.region initial 1264, by simp,
      stack_layout_within pre.stack layout rspC outputC region member a contains⟩)
  have preservedSaved : (Component.mem (stackPtr initial - 40) 48).Agrees c t :=
    frame_agrees_of_disjoint result.frame (by
      rw [show (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 from
        stack_sub_toNat pre.stack (by decide : 40 ≤ 1264)]
      have bound := stack_bounds pre.stack
      omega)
      (stack_layout_disjoint pre.stack layout rspC outputC (.inl (by decide)) (by decide))
  have callSaved : (Component.mem (stackPtr initial - 40) 48).Agrees s c := by
    have same := call_local_agrees called 368 48
      (by unfold OffsetsApart; decide +kernel) (by decide)
    rw [show stackPtr s + BitVec.ofNat 64 368 = stackPtr initial - 40 by
      rw [state.rsp]; bv_omega] at same
    exact same
  have complete := call_result callee called result.toCalleeResult state.running.directionFlag
  refine ⟨t, state.of_running runningT complete.2
    (result.rsp.trans (congrArg ReturnBoundary.rsp returnC))
    (fun i hi ↦ (preservedSaved i hi).trans (callSaved i hi)), ?_, ?_⟩
  · rw [result.rip, returnC]
    rfl
  · simpa only [outputC, compressBlocks_single hash block bytes.1] using result.hashWords

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Compression
