import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls
import Hkdf.Proofs.Common.SHA256.Correctness

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def compressionLayout : StackCallLayout 2264 0 32 336 :=
  ⟨544, 0, 200, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private def bufferLayout : StackCallLayout 2264 64 32 336 :=
  ⟨544, 264, 200, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

def compressionRegions (s : RamState) : Vector MemoryRegion 2 :=
  #v[⟨(stackPtr s + 336).toNat, 32⟩, ⟨(stackPtr s).toNat - 344, 344⟩]

set_option maxRecDepth 2048 in
theorem compressionCall [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info input : ByteArray} {ptr : BitVec 64} {length count : Nat} {hash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (buffered : Bool)
    (pc : s.RIP = if buffered then 0x10f77d else 0x10f7a9)
    (dest : s.regValue .rdi = stackPtr s + 336)
    (countArg : s.regValue .rdx = BitVec.ofNat 64 count)
    (words : HashStateAt s (stackPtr s + 336) hash)
    (bytes : (registerRegion s .rsi (64 * count)).HasBytes s.external input)
    (source : (s.regValue .rsi = stackPtr s + 272 ∧ count = 1) ∨
      ((registerRegion s .rsi (64 * count)).Bounded ∧
       (registerRegion s .rsi (64 * count)).Allocated s.external ∧
       (registerRegion s .rsi (64 * count)).Disjoint (Stack.region entry 2264))) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = (if buffered then 0x10f782 else 0x10f7ae) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t (compressionRegions s) ∧
      HashStateAt t (stackPtr s + 336) (compressBlocks hash input) := by
  let off : Nat := if buffered then 0xf77d else 0xf7a9
  let p := Extracted.textAddress + BitVec.ofNat 64 off
  let disp : BitVec 32 := if buffered then 0xffff9e3e else 0xffff9e12
  let ret : BitVec 64 := if buffered then 0x10f782 else 0x10f7ae
  have stack := pre.call.stack
  have avoid := pre.call.stackAvoid
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have push : pushAddr s = stackPtr entry - 544 := by rw [pushAddr, sp, BitVec.sub_sub]; rfl
  have ins := programText_slice (programLoaded_codeIn saved.loaded) off (encodeCallRel32 disp)
    (by cases buffered <;> decide) (by cases buffered <;> decide +kernel)
  have step : StepEffect (PushPre p 5) (codeRange p (encodeCallRel32 disp))
      (callEffect (fun _ ↦ 0x1095c0) ret) := by
    cases buffered
    · exact call_rel32_effect_step 0x10f7a9 0xffff9e12 (by decide +kernel)
    · exact call_rel32_effect_step 0x10f77d 0xffff9e3e (by decide +kernel)
  have hp : PushPre p 5 s := by
    refine ⟨by cases buffered <;> exact pc, ?_, ?_⟩
    · rw [push]
      exact stack_writable8 stack avoid saved.allocated (offset := 544) (by decide) (by decide)
    · rw [push]
      exact stack_codeApart stack (fun a ha h ↦ avoid a ha (.inl h)) (offset := 544)
        (codeOffset := off) (by decide) (by decide) (by cases buffered <;> decide)
  obtain ⟨c, callRun, ready, call⟩ := step.advances (supportedMachine_readyToStep saved.machine)
    ins hp (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
  have writes : WritesWithin (callEffect (fun _ ↦ 0x1095c0) ret s).components
      #v[Stack.region entry 2264] := by
    intro component member a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ha.elim
    · rw [push] at ha
      exact ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 (offset := 544) (by decide) (by decide) ha⟩
    · exact ha.elim
  have localRun := (Running.initial (regions := #v[Stack.region entry 2264]) saved.machine
    saved.loaded saved.directionFlag).of_agrees callRun ready call.agrees writes (by
      intro r hr a ha h
      obtain rfl := Vector.mem_singleton.mp hr
      exact avoid a ha (.inl h)) (by simp [callEffect, pushEffect_components])
  have boundaryC := call_boundary call
  have rspC : stackPtr c = stackPtr entry - 544 := call.writes.1.trans push
  have outC : c.regValue .rdi = stackPtr s + 336 :=
    (call.agrees.read (r := 7) (n := 64) (by simp [callEffect, pushEffect_components])).trans dest
  have out : c.regValue .rdi = stackPtr entry - 200 := by rw [outC, sp]; bv_omega
  have src : c.regValue .rsi = s.regValue .rsi :=
    call.agrees.read (r := 6) (n := 64) (by simp [callEffect, pushEffect_components])
  have regionEq : registerRegion c .rsi (64 * count) = registerRegion s .rsi (64 * count) := by
    simp only [registerRegion, src]
  have grow (a : BitVec 64) (h : (entry.external[a]?).isSome) :=
    localRun.allocated a (saved.allocated a h)
  have returnIn : InProgram (returnBoundary c).rip := by
    rw [boundaryC]
    cases buffered
    · exact inProgram_of_textOffset 0xf7ae (by decide)
    · exact inProgram_of_textOffset 0xf782 (by decide)
  have callee : CalleePre c boundary 0x1095c0 (64 * count) 32 336 := by
    rcases source with ⟨buffer, rfl⟩ | ⟨bounded, allocated, apart⟩
    · apply callee_pre_of_stack pre.call.stride stack avoid pre.call.outerBoundary localRun.machine
        localRun.directionFlag localRun.loaded grow bufferLayout call.rip rspC _ out returnIn
      change c.regValue .rsi = stackPtr entry - 264
      rw [src, buffer, sp]
      bv_omega
    · apply callee_pre_of_stack_output pre.call.stride stack avoid pre.call.outerBoundary localRun.machine
        localRun.directionFlag localRun.loaded grow compressionLayout call.rip rspC out returnIn
      · rwa [regionEq]
      · rw [regionEq]
        intro a ha
        exact Option.isSome_iff_exists.mp (localRun.allocated a (Option.isSome_iff_exists.mpr (allocated a ha)))
      · rwa [regionEq]
  have bytesC : (registerRegion c .rsi (64 * count)).HasBytes c.external input := by
    apply frame_hasBytes (call_frame callee.stack call)
    · intro r member
      obtain rfl := Vector.mem_singleton.mp member
      exact callee.separation (0 : Fin 3) (2 : Fin 3) (by decide)
    · have h := callee.inputBounded
      change _ < 2^32 at h
      omega
    · rwa [regionEq]
  have comp : CompressionPre c boundary hash input count := by
    refine ⟨callee, ?_, ?_, bytesC, ?_⟩
    · rw [out]
      change (stackPtr entry - BitVec.ofNat 64 200).toNat % 4 = 0
      rw [stack_sub_toNat stack (offset := 200) (by decide)]
      have := stack_bounds stack
      have align : (stackPtr entry).toNat % 16 = 8 := stack.2.2.2
      omega
    · exact (call.agrees.read (r := 2) (n := 64) (by simp [callEffect, pushEffect_components])).trans countArg
    · rw [outC]
      exact hashState_of_bytes words (StreamPadding.Execution.call_local_agrees call 336 32
        (by unfold OffsetsApart; decide +kernel) (by decide))
  obtain ⟨t, result⟩ := compression_correct comp
  have within := stack_layout_within stack compressionLayout rspC out
  have localT := localRun.of_callee result.toCalleeResult (by
    intro r hr a inside
    exact ⟨_, by simp, within r hr a inside⟩)
  obtain ⟨frame, abi⟩ := call_result callee call result.toCalleeResult saved.directionFlag
  have spT : stackPtr t = stackPtr s := result.rsp.trans (congrArg ReturnBoundary.rsp boundaryC)
  obtain ⟨oldFuel, oldRun⟩ := saved.execution
  obtain ⟨fuel, run⟩ := localT.execution
  have running : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t :=
    ⟨⟨_,oldRun.trans run⟩, localT.machine, localT.loaded, fun a h ↦ localT.allocated a (saved.allocated a h),
      localT.directionFlag, memoryWriteFrame_trans saved.frame (frame_mono localT.frame (by
        intro r hr a h
        obtain rfl := Vector.mem_singleton.mp hr
        exact ⟨_, by simp, h⟩))⟩
  have keep (k n : Nat) (apart : k + 32 ≤ 200 ∨ 200 + n ≤ k) (low : k + 8 ≤ 544)
      (high : n ≤ k + 8) : (Component.mem (stackPtr entry - BitVec.ofNat 64 k) n).Agrees s t := by
    apply frame_agrees_of_disjoint frame
    · rw [stack_sub_toNat stack (offset := k) (by omega)]
      have := stack_bounds stack
      omega
    · exact stack_layout_disjoint stack compressionLayout rspC out apart low
  have savedT := saved.of_agreement running spT (by
    change (Component.mem (stackPtr s + 488) 56).Agrees s t
    rw [show stackPtr s + 488 = stackPtr entry - 48 from by rw [sp]; bv_omega]
    exact keep 48 56 (by decide) (by decide) (by decide)) (by
    change memLoad t.external (stackPtr t + 224) 64 = memLoad s.external (stackPtr s + 224) 64
    rw [spT, show stackPtr s + 224 = stackPtr entry - 312 from by rw [sp]; bv_omega]
    exact agrees_memLoad (keep 312 8 (by decide) (by decide) (by decide))) abi.2.2.1 abi.2.2.2
  refine ⟨t, savedT, ⟨fuel,run⟩, result.rip.trans (congrArg ReturnBoundary.rip boundaryC), abi, ?_, ?_⟩
  · have geom := stack_layout_bounds stack compressionLayout rspC out
    have start : (Stack.region c 336).start = (stackPtr entry).toNat - 880 := geom.2.1
    have finish : (Stack.region c 336).start + (Stack.region c 336).size = (stackPtr entry).toNat - 544 + 8 :=
      geom.2.2
    have hsp := stack_sub_toNat stack (offset := 536) (by decide)
    change (stackPtr entry - 536).toNat = (stackPtr entry).toNat - 536 at hsp
    have := stack_bounds stack
    have same : Stack.region c 336 = ⟨(stackPtr s).toNat - 344,344⟩ := by
      cases h : Stack.region c 336 with
      | mk a n =>
        rw [h] at start finish
        change a = _ at start
        change a + n = _ at finish
        rw [sp]
        have ha : a = (stackPtr entry - 536).toNat - 344 := by omega
        have hn : n = 344 := by omega
        rw [ha, hn]
    simpa only [compressionRegions, registerRegion, outC, same] using frame
  · simpa only [outC] using result.hashWords

end Hkdf.Proofs.NewExpand.Expand.Info
