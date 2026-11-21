import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Compression

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Program Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.StreamPadding.Execution

def hashOffset (outer : Bool) : Nat := if outer then 8 else 248

private def layout (outer : Bool) : StackCallLayout 1264 64 32 336 :=
  ⟨416, 336, 408-hashOffset outer, by decide, by decide, by decide,
    by cases outer <;> decide, by decide, by cases outer <;> decide,
    by cases outer <;> decide⟩

private def pc (outer : Bool) : BitVec 64 := if outer then 0x10e1aa else 0x10e154

private def displacement (outer : Bool) : BitVec 32 :=
  if outer then 0xffffb411 else 0xffffb467

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {block : ByteArray} {hash : Array UInt32}
    (outer : Bool) (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (running : Running initial boundary
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] s)
    (rsp : stackPtr s = stackPtr initial - 408)
    (rip : s.RIP = if outer then 0x10e1aa else 0x10e154)
    (destination : s.regValue .rdi = stackPtr s + if outer then 8 else 248)
    (source : s.regValue .rsi = stackPtr s + 72)
    (count : s.regValue .rdx = 1)
    (bytes : (MemoryRegion.mk (stackPtr s + 72).toNat 64).HasBytes s.external block)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 (hashOffset outer)) hash) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary #v[registerRegion initial .rdi 176, Stack.region initial 1264] t ∧
      t.RIP = (if outer then 0x10e1af else 0x10e159) ∧
      stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[
        MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 (hashOffset outer)).toNat 32,
        MemoryRegion.mk (stackPtr s - 344).toNat 344] ∧
      HashStateAt t (stackPtr s + BitVec.ofNat 64 (hashOffset outer))
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  have avoid := pre.avoids (Stack.region initial 1264) (by simp)
  have step := call_rel32_effect_step (pc outer) (displacement outer)
    (by cases outer <;> decide +kernel)
  have target : branchTarget (pc outer) 5 ((displacement outer).signExtend 64) = 0x1095c0 := by
    cases outer <;> decide +kernel
  have instruction : CodeIn (codeRange (pc outer) (encodeCallRel32 (displacement outer))) s := by
    cases outer
    · exact programText_slice (programLoaded_codeIn running.loaded) 0xe154 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0xe1aa _
        (by decide) (by decide +kernel)
  have conditions : PushPre (pc outer) 5 s := by
    refine ⟨rip, call_writable .hmac pre running rsp, ?_⟩
    cases outer
    · exact call_codeApart .hmac pre rsp 0xe154 5 (by decide)
    · exact call_codeApart .hmac pre rsp 0xe1aa 5 (by decide)
  obtain ⟨c, callRun, readyC, called⟩ := step.advances
    (supportedMachine_readyToStep running.machine) instruction conditions
    (by rw [target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
  have runningC := running.of_agrees callRun readyC called.agrees (by
    intro component member a covered
    obtain ⟨region, hr, contains⟩ := call_writes .hmac pre rsp _ _ component member a covered
    exact writes_within_regions .hmac pre region hr a.toNat contains) (regions_avoids .hmac pre)
    (by simp [callEffect, pushEffect_components])
  have rspC : stackPtr c = stackPtr initial - 416 :=
    called.writes.1.trans (by change stackPtr s - 8 = _; rw [rsp, BitVec.sub_sub]; rfl)
  have returnC := call_boundary called
  have outputAddress : c.regValue .rdi = stackPtr s + BitVec.ofNat 64 (hashOffset outer) := by
    apply (called.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans
    cases outer <;> exact destination
  have outputC : c.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (408 - hashOffset outer) := by
    rw [outputAddress, rsp]
    exact local_address .hmac pre _ (by cases outer <;> decide)
  have inputAddress : c.regValue .rsi = stackPtr s + 72 :=
    (called.agrees.read (n := 64) (r := 6)
      (by simp [callEffect, pushEffect_components])).trans source
  have sourceC : c.regValue .rsi = stackPtr initial - 336 := by
    rw [inputAddress, rsp]
    exact local_address .hmac pre 72 (by decide)
  have countC : c.regValue .rdx = 1 :=
    (called.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans count
  have callee : CalleePre c boundary 0x1095c0 64 32 336 := by
    apply callee_pre_of_stack pre.stride pre.stack avoid pre.outerBoundary
      runningC.machine runningC.directionFlag runningC.loaded runningC.allocated
      (layout outer) (called.rip.trans target) rspC sourceC outputC
    rw [returnC]
    cases outer
    · exact inProgram_of_textOffset 0xe159 (by decide)
    · exact inProgram_of_textOffset 0xe1af (by decide)
  have hashC : HashStateAt c (c.regValue .rdi) hash := by
    rw [outputAddress]
    exact hashState_of_bytes words (call_local_agrees called (hashOffset outer) 32
      (by cases outer <;> unfold OffsetsApart <;> decide +kernel) (by decide))
  have bytesC : (registerRegion c .rsi 64).HasBytes c.external block := by
    change (MemoryRegion.mk (c.regValue .rsi).toNat 64).HasBytes _ _
    rw [inputAddress]
    have same := call_local_agrees called 72 64 (by unfold OffsetsApart; decide +kernel) (by decide)
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 64 := (show block.size = 64 from bytes.1) ▸ i.isLt
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using
      (same i.val hi).trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using bytes.2 i)
  have compression : Hkdf.Proofs.Common.SHA256.CompressionPre c boundary hash block 1 := by
    refine ⟨callee, ?_, countC, bytesC, hashC⟩
    rw [outputC, CallFrame.stack_sub_toNat pre.stack (by cases outer <;> decide)]
    have aligned : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
    have bounds := stack_bounds pre.stack
    cases outer <;> simp only [hashOffset, Bool.false_eq_true, ite_false, ite_true,
      Nat.reduceSub] <;> omega
  obtain ⟨t, result⟩ := Hkdf.Proofs.Common.SHA256.compression_correct compression
  have within := stack_layout_within pre.stack (layout outer) rspC outputC
  have runningT := runningC.of_callee result.toCalleeResult (by
    intro region member a contains
    exact ⟨Stack.region initial 1264, by simp, within region member a contains⟩)
  have complete := call_result callee called result.toCalleeResult running.directionFlag
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨1+fuel, t, callRun.trans execution, supportedMachine_readyToStep result.machine,
    runningT, ?_, ?_, complete.2, ?_, ?_⟩
  · rw [result.rip, returnC]
    cases outer <;> rfl
  · exact result.rsp.trans (congrArg ReturnBoundary.rsp returnC)
  · have stackRegion : Stack.region c 336 = MemoryRegion.mk (stackPtr s-344).toNat 344 := by
      rw [rsp]
      exact Common.StreamPadding.Execution.call_stack_region .hmac pre (by
        change stackPtr c = stackPtr initial - 408 - 8
        rw [rspC, BitVec.sub_sub]
        rfl) 336 (by decide)
    simpa only [registerRegion, outputAddress, stackRegion] using complete.1
  · simpa only [outputAddress, compressBlocks_single hash block bytes.1] using result.hashWords

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Compression
