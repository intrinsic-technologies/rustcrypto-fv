import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.InnerPrefix.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Block

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPrefix

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.StreamPadding
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem copy_cover {s : RamState} {c : Component} {a : BitVec 64}
    (hc : c ∈ (Extra.copyLengthEffect s).components) (ha : c.Covers a) :
    (Component.mem (stackPtr s + 72) 8).Covers a := by
  simp only [Extra.copyLengthEffect, Effect.components, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component_reg,
    Write.component_mem, Nat.reduceDiv] at hc
  rcases hc with (rfl | rfl) | rfl
  · exact ha.elim
  · exact ha
  · exact ha.elim

private theorem above_disjoint {p : BitVec 64} {off len other size : Nat}
    (high : p.toNat + 544 < 2^32) (below : other + size ≤ off) (bound : off + len ≤ 544) :
    ∀ r ∈ #v[⟨(p + BitVec.ofNat 64 other).toNat, size⟩],
      (⟨(p + BitVec.ofNat 64 off).toNat, len⟩ : MemoryRegion).Disjoint r := by
  intro r member a inside changed
  obtain rfl := Vector.mem_singleton.mp member
  change (p + BitVec.ofNat 64 off).toNat ≤ a ∧ a < (p + BitVec.ofNat 64 off).toNat + len at inside
  change (p + BitVec.ofNat 64 other).toNat ≤ a ∧ a < (p + BitVec.ofNat 64 other).toNat + size at changed
  rw [add_toNat high off (by omega)] at inside
  rw [add_toNat high other (by omega)] at changed
  omega

private theorem compression_frame {s t : RamState} (high : (stackPtr s).toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (CompressionSite.blockWrites .extra (stackPtr s))) :
    MemoryWriteFrame s t (writes (stackPtr s)) := by
  apply frame_mono frame
  intro r member a inside
  have cases : r = ⟨(stackPtr s + 16).toNat, 56⟩ ∨
      r = ⟨(stackPtr s + 144).toNat, 32⟩ ∨ r = ⟨(stackPtr s).toNat - 344, 344⟩ := by
    simpa [CompressionSite.blockWrites, CompressionSite.hashOffset] using member
  rcases cases with rfl | rfl | rfl
  · exact include_above high (off := 16) (by decide) (by decide) inside
  · exact include_above high (off := 144) (by decide) (by decide) inside
  · exact ⟨_, by simp [writes], inside⟩

theorem Result.agrees_stack [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {n offset size : Nat} {regions : Vector MemoryRegion n} {message : ByteArray}
    (result : Result entry s t boundary regions message) (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) (bound : offset + size ≤ 544)
    (apart : offset + size ≤ 16 ∨ 176 ≤ offset) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) size).Agrees s t := by
  obtain ⟨_, low, high⟩ := stack_geometry stack sp
  have address := add_toNat high offset (by omega)
  apply frame_agrees_of_disjoint result.frame
  · rw [address]
    omega
  · intro r member a preserved changed
    have cases : r = ⟨(stackPtr s).toNat - 344, 344⟩ ∨ r = ⟨(stackPtr s).toNat + 16, 160⟩ := by
      simpa [writes] using member
    change (stackPtr s + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 offset).toNat + size at preserved
    rw [address] at preserved
    rcases cases with rfl | rfl
    · change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at changed
      rw [Nat.sub_add_cancel low] at changed
      omega
    · change (stackPtr s).toNat + 16 ≤ a ∧ a < (stackPtr s).toNat + 16 + 160 at changed
      omega

theorem run [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info message : ByteArray} {ptr : BitVec 64} {length n : Nat}
    {regions : Vector MemoryRegion n}
    (pre : ExpandPre entry boundary key info ptr length) (running : Running entry boundary regions s)
    (inStack : Stack.region entry 2264 ∈ regions) (avoids : ∀ r ∈ regions, r.Avoids InProgram)
    (sp : stackPtr s = stackPtr entry - 536) (pc : s.RIP = 0x10f95a)
    (stream : StreamAt s (stackPtr s + 80) message) :
    ∃ t, Result entry s t boundary regions message := by
  have stack := pre.call.stack
  have avoid := pre.call.stackAvoid
  have outside := pre.call.outerBoundary
  have avoidCode : (Stack.region entry 2264).Avoids InProgram := fun a ha hp => avoid a ha (.inl hp)
  obtain ⟨_, low, high⟩ := stack_geometry stack sp
  obtain ⟨a, marked⟩ := InnerPadding.run stack avoid inStack avoids outside pre.call.stride running sp pc stream
  have aFrame := mark_frame low high marked.frame
  by_cases small : message.size % 64 < 56
  · have bytes : (⟨(stackPtr a + 80).toNat, 56⟩ : MemoryRegion).HasBytes a.external (finalPrefix message) := by
      rw [← paddedBuffer_prefix message small]
      exact Common.Memory.hasBytes_prefix marked.padded (by change 56 ≤ 64; decide)
    exact ⟨a, ⟨marked.execution, marked.running, by simpa only [small, ite_true] using marked.rip,
      marked.rsp, marked.blocks, marked.length, marked.r12, marked.r14, marked.rbp, marked.mxcsr, marked.fcw,
      aFrame, by simpa only [prefixHash, small, ite_true] using marked.hash, bytes⟩⟩
  have aSp := marked.rsp.trans sp
  have highA : (stackPtr a).toNat + 544 < 2^32 := by rw [marked.rsp]; exact high
  have read136 : rspOf a + 136 = stackPtr entry - 400 :=
    InnerPadding.local_address aSp 136 (by decide)
  have write72 : rspOf a + 72 = stackPtr entry - 464 :=
    InnerPadding.local_address aSp 72 (by decide)
  have copyPre : Extra.CopyLengthPre a := by
    refine ⟨by simpa only [small, ite_false] using marked.rip, ?_, ?_, ?_⟩
    · rw [read136]
      exact stack_readable stack marked.running.allocated (by decide) (by decide)
    · rw [write72]
      exact stack_writable8 stack avoid marked.running.allocated (by decide) (by decide)
    · rw [write72]
      exact stack_codeApart (codeOffset := 0xf995) stack avoidCode (by decide) (by decide) (by decide)
  obtain ⟨_, b, copy, readyB, copied⟩ := Extra.copyLength
    (supportedMachine_readyToStep marked.running.machine) marked.running.loaded outside copyPre
  obtain ⟨runningB, copyFrame⟩ := step_frame stack aSp marked.running inStack avoids copy readyB copied.agrees
    (by simp [Extra.copyLengthEffect, Effect.components]) (off := 72) (len := 8)
    (by decide) (by decide) (fun _ hc _ ha => copy_cover hc ha)
  have bSp : stackPtr b = stackPtr a :=
    copied.agrees.read (n := 64) (r := 4) (by simp [Extra.copyLengthEffect, Effect.components])
  have kept (off size : Nat) (above : 80 ≤ off) (fit : off + size ≤ 544) :
      (Component.mem (stackPtr a + BitVec.ofNat 64 off) size).Agrees a b := by
    apply frame_agrees_of_disjoint copyFrame
    · rw [add_toNat highA off (by omega)]
      omega
    · exact above_disjoint highA (by omega) fit
  have eighth : slot b 72 = slot b 136 := by
    change memLoad b.external (stackPtr b + 72) 64 = memLoad b.external (stackPtr b + 136) 64
    rw [bSp]
    exact copied.writes.2.trans (agrees_memLoad (kept 136 8 (by decide) (by decide))).symm
  have padded : (⟨(stackPtr b + 80).toNat, 64⟩ : MemoryRegion).HasBytes b.external (tailFirst message) := by
    rw [bSp, show tailFirst message = paddedBuffer message by
      simp only [tailFirst, paddedBuffer, small, ite_false]]
    apply frame_hasBytes copyFrame
    · exact above_disjoint highA (off := 80) (len := 64) (by decide) (by decide)
    · change (stackPtr a + BitVec.ofNat 64 80).toNat + 64 ≤ 2^64
      rw [add_toNat highA 80 (by decide)]
      omega
    · exact marked.padded
  have hashB : HashStateAt b (stackPtr b + BitVec.ofNat 64 (CompressionSite.hashOffset .extra))
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) := by
    rw [bSp]
    exact hashState_of_bytes marked.hash (kept 144 32 (by decide) (by decide))
  obtain ⟨c, localC, cRip, cSp, cRegs, cMXCSR, cFCW, hashC⟩ := compressBlock pre runningB
    inStack avoids (bSp.trans aSp) .extra copied.rip (by intro impossible; cases impossible)
    padded eighth hashB
  have compFrame := compression_frame (by rw [bSp]; exact highA) localC.frame
  have runningC := append_running stack (bSp.trans aSp) inStack runningB
    ⟨localC.execution, localC.machine, localC.loaded, localC.allocated, localC.directionFlag, compFrame⟩
  have cSpEntry := cSp.trans (bSp.trans aSp)
  have highC : (stackPtr c).toNat + 544 < 2^32 := by rw [cSp, bSp]; exact highA
  have zeroPre : Extra.ZeroPre c := by
    refine ⟨cRip, ?_, ?_⟩
    · intro i hi
      change MemWritable c (stackPtr c + BitVec.ofNat 64 (80 + 8*i)) 8
      rw [InnerPadding.local_address cSpEntry _ (by omega)]
      exact stack_writable8 stack avoid runningC.allocated (by omega) (by omega)
    · intro i hi
      change RangeApart (stackPtr c + BitVec.ofNat 64 (80 + 8*i)) 8 0x10fa02 71
      rw [InnerPadding.local_address cSpEntry _ (by omega)]
      exact stack_codeApart (codeOffset := 0xfa02) stack avoidCode (by omega) (by omega) (by decide)
  obtain ⟨_, t, zero, readyT, zeroed, tBytes⟩ := Extra.zeroPrefix
    (supportedMachine_readyToStep runningC.machine) runningC.loaded outside zeroPre
  obtain ⟨runningT, zeroFrame⟩ := step_frame stack cSpEntry runningC inStack avoids zero readyT zeroed.agrees
    (by simp [Extra.zeroEffect, Effect.components]) (off := 80) (len := 56)
    (by decide) (by decide) (fun _ hc _ ha => Extra.zero_memory_footprint hc ha)
  have tSp : stackPtr t = stackPtr c :=
    zeroed.agrees.read (n := 64) (r := 4) (by simp [Extra.zeroEffect, Effect.components])
  have regs (r : Syntax.Reg) (member : r ∈ ([.rbx,.rbp,.r12,.r13,.r14,.r15] : List Syntax.Reg)) :
      t.regValue r = a.regValue r := by
    refine (reg_agrees zeroed.agrees r (by simp [Extra.zeroEffect, Effect.components])).trans
      ((cRegs r member).trans (reg_agrees copied.agrees r ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Extra.copyLengthEffect, Effect.components, regIndex] <;> decide
  have tHash : HashStateAt t (stackPtr t + 144) (prefixHash message) := by
    rw [tSp, prefixHash, ite_eq_right small]
    have words := hashC
    change HashStateAt c (stackPtr b + 144) _ at words
    rw [← cSp] at words
    have same : (Component.mem (stackPtr c + 144) 32).Agrees c t :=
      frame_agrees_of_disjoint zeroFrame
        (by
          change (stackPtr c + BitVec.ofNat 64 144).toNat + 32 ≤ 2^64
          rw [add_toNat highC 144 (by decide)]
          omega)
        (above_disjoint highC (by decide) (by decide : 144 + 32 ≤ 544))
    exact hashState_of_bytes words same
  have tFrame := memoryWriteFrame_trans aFrame (memoryWriteFrame_trans
    (by simpa only [marked.rsp] using step_widen highA (by decide) (by decide) copyFrame)
    (memoryWriteFrame_trans (by simpa only [bSp, marked.rsp] using compFrame)
      (by simpa only [cSp, bSp, marked.rsp] using step_widen highC (by decide) (by decide) zeroFrame)))
  obtain ⟨_, markExec⟩ := marked.execution
  obtain ⟨_, compExec⟩ := localC.execution
  refine ⟨t, ⟨⟨_, ((markExec.trans copy).trans compExec).trans zero⟩, runningT, zeroed.rip,
    tSp.trans (cSp.trans (bSp.trans marked.rsp)),
    (regs .r13 (by decide)).trans marked.blocks, (regs .r15 (by decide)).trans marked.length,
    (regs .r12 (by decide)).trans marked.r12, (regs .r14 (by decide)).trans marked.r14,
    (regs .rbp (by decide)).trans marked.rbp, ?_, ?_, tFrame, tHash, ?_⟩⟩
  · exact (zeroed.agrees.mxcsr (by simp [Extra.zeroEffect, Effect.components])).trans
      (cMXCSR.trans ((copied.agrees.mxcsr (by simp [Extra.copyLengthEffect, Effect.components])).trans marked.mxcsr))
  · exact (zeroed.agrees.fcw (by simp [Extra.zeroEffect, Effect.components])).trans
      (cFCW.trans ((copied.agrees.fcw (by simp [Extra.copyLengthEffect, Effect.components])).trans marked.fcw))
  · rw [tSp, finalPrefix, ite_eq_right small]
    exact tBytes

end Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPrefix
