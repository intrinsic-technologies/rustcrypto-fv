import Hkdf.Proofs.Key.Hash.State
import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail
import Hkdf.Proofs.Common.Memory
import Hkdf.Proofs.Common.State

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Program (PreservesABI)

set_option maxHeartbeats 800000 in
theorem compression_call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} {hash : Array UInt32} {count : Nat}
    (ctx : Context initial boundary key) (state : Working initial boundary s)
    (offset : Nat) (disp : BitVec 32) (outputOffset : Nat)
    (offsetBound : offset + 5 < 115149)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x1095c0)
    (slice : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : 72 ≤ outputOffset) (outputLow : outputOffset ≤ 312)
    (aligned : outputOffset % 4 = 0)
    (words : HashStateAt s (s.regValue .rdi) hash)
    (countRegister : s.regValue .rdx = BitVec.ofNat 64 count)
    (prepare : ∀ u, Running initial boundary (writeRegions initial) u →
      (callEffect (fun _ ↦ 0x1095c0)
        (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5) s).Holds s u →
      returnBoundary u = ⟨Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5, stackPtr s⟩ →
      Hkdf.Proofs.Common.Machine.CalleePre u boundary 0x1095c0 (64 * count) 32 336 ∧
        (registerRegion u .rsi (64 * count)).HasBytes u.external input) :
    ∃ t, Working initial boundary t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5 ∧
      HashStateAt t (s.regValue .rdi) (compressBlocks hash input) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t
        #v[registerRegion s .rdi 32, ⟨(stackPtr initial - BitVec.ofNat 64 720).toNat, 344⟩] := by
  have push : pushAddr s = stackPtr initial - 384 := by
    change stackPtr s - 8 = _
    rw [state.rsp]
    simp only [blockAddress, BitVec.sub_sub]
    rfl
  have instruction := programText_slice (programLoaded_codeIn state.loaded) offset
    (encodeCallRel32 disp) (by change offset + 5 ≤ 115149; omega) (by change Extracted.textBytes.toListFrom offset 5 = _; exact slice)
  have step : StepEffect (PushPre (Extracted.textAddress + BitVec.ofNat 64 offset) 5)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) (encodeCallRel32 disp))
      (callEffect (fun _ ↦ 0x1095c0)
        (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5)) := by
    simpa only [target] using call_rel32_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 offset) disp (by rw [target]; decide)
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 ctx state.toState (offset := 384) (by decide) (by decide)
  have separate : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) 5 := by
    rw [push]
    exact stack_codeApart ctx (offset := 384) (by decide) (by decide) (by omega)
  have writes : WritesWithin
      (callEffect (fun _ ↦ 0x1095c0)
        (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5) s).components
      (writeRegions initial) := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, push, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨Stack.region initial stackBytes, by simp [writeRegions],
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.stack.2.2.1
        (offset := 384) (by decide) (by decide) ha⟩
  obtain ⟨u, runningU, call, ret⟩ := state.toRunning.call step instruction
    ⟨rip, writable, separate⟩
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
    writes (by
      intro region member address contains inside
      exact ctx.avoids region (by simpa [writeRegions] using member) address contains (.inl inside))
  obtain ⟨pre, inputBytes⟩ := prepare u runningU call ret
  have rspU : stackPtr u = stackPtr initial - 384 := call.writes.1.trans push
  have pointer : u.regValue .rdi = s.regValue .rdi := call.agrees.read
    (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])
  have outputU := pointer.trans output
  let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 0 32 336 :=
    ⟨384, 0, outputOffset, by decide, by decide, by decide, by omega,
      by decide, by omega, .inr (by omega)⟩
  have callWrites : WritesWithin
      (callEffect (fun _ ↦ 0x1095c0)
        (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 5) s).components
      #v[Stack.region u 336] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨Stack.region u 336, by simp, ?_⟩
    rw [show pushAddr s = stackPtr u from call.writes.1.symm] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact Hkdf.Proofs.Common.Machine.memoryRegion_contains_add pre.stack.1
      (len := 8) (by change (stackPtr u).toNat - 336 ≤ (stackPtr u).toNat; omega)
      (by rw [Hkdf.Proofs.Common.Machine.stack_region_end]; exact Nat.le_refl _) hi
  have callFrame := call.agrees.memoryWriteFrame callWrites
  have sameOutput : (Component.mem (s.regValue .rdi) 32).Agrees s u := by
    apply frame_agrees callFrame
    intro a covered region member contains
    have eq : region = Stack.region u 336 := by simpa using member
    subst region
    obtain ⟨i, hi, rfl⟩ := covered
    apply pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) _ ?_ contains
    rw [← pointer]
    exact Hkdf.Proofs.Common.Machine.memoryRegion_contains_add pre.outputBounded
      (len := 32) (Nat.le_refl _) (Nat.le_refl _) hi
  have compressionPre : Hkdf.Proofs.Common.SHA256.CompressionPre u boundary
      hash input count := {
    toCalleePre := pre
    hashAligned := by
      rw [outputU, stack_sub_toNat ctx.toCalleePre (offset := outputOffset) (by change outputOffset ≤ 720; omega)]
      have bounds := stack_bounds ctx.toCalleePre
      have stackAligned : (stackPtr initial).toNat % 16 = 8 := ctx.stack.2.2.2
      omega
    countRegister := (call.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans countRegister
    inputBytes := inputBytes
    hashWords := by
      rw [pointer]
      exact Hkdf.Proofs.Common.hashState_of_bytes words sameOutput
  }
  obtain ⟨t, result⟩ := Hkdf.Proofs.Common.SHA256.compression_correct compressionPre
  have within := stack_layout_within ctx.stack layout rspU outputU
  have runningT := runningU.of_callee result.toCalleeResult (by
    intro region member a contains
    exact ⟨Stack.region initial stackBytes, by simp [writeRegions], within region member a contains⟩)
  have bounds := stack_bounds ctx.toCalleePre
  change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
  have frame : MemoryWriteFrame s t #v[registerRegion u .rdi 32, Stack.region u 336] :=
    memoryWriteFrame_trans (frame_mono callFrame (by
      intro region member a contains
      refine ⟨region, ?_, contains⟩
      have eq : region = Stack.region u 336 := by simpa using member
      subst region
      simp)) result.frame
  have saved := frame_agrees_of_disjoint frame
    (address := stackPtr initial - 40) (size := 48)
    (by
      change (stackPtr initial - BitVec.ofNat 64 40).toNat + 48 ≤ 2^64
      rw [stack_sub_toNat ctx.toCalleePre (offset := 40) (by decide)]
      omega)
    (stack_layout_disjoint ctx.stack layout rspU outputU
      (savedOffset := 40) (savedBytes := 48) (.inl (by dsimp only [layout]; omega)) (by change 40 + 8 ≤ 384; decide))
  have zero := frame_hasBytes frame
    (stack_layout_disjoint ctx.stack layout rspU outputU
      (savedOffset := 376) (savedBytes := 64) (.inr (by dsimp only [layout]; omega)) (by change 376 + 8 ≤ 384; decide))
    (by
      change (stackPtr initial - BitVec.ofNat 64 376).toNat + 64 ≤ 2^64
      rw [stack_sub_toNat ctx.toCalleePre (offset := 376) (by decide)]
      omega)
    state.zeroBlock
  have abiCall : PreservesABI s u := by
    apply Hkdf.Proofs.Common.Machine.preservesABI_of_agrees call.agrees state.directionFlag
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact call.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 12) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 13) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 14) (by simp [callEffect, pushEffect_components])
      · exact call.agrees.read (n := 64) (r := 15) (by simp [callEffect, pushEffect_components])
    all_goals simp [callEffect, pushEffect_components]
  have abi := Hkdf.Proofs.Common.Machine.preservesABI_trans abiCall result.abi
  have rspT : stackPtr t = stackPtr s := by
    rw [show stackPtr t = (returnBoundary u).rsp from result.rsp, ret]
  have working := state.of_observations runningT saved rspT (abi.1 .rbx (by simp))
    (abi.1 .rbp (by simp)) abi.2.2.1 abi.2.2.2 zero
  have stackRegion : Stack.region u 336 =
      (⟨(stackPtr initial - BitVec.ofNat 64 720).toNat, 344⟩ : MemoryRegion) := by
    have sp : (stackPtr u).toNat = (stackPtr initial).toNat - 384 := by
      rw [rspU]
      exact stack_sub_toNat ctx.toCalleePre (by decide)
    have base := stack_sub_toNat ctx.toCalleePre (offset := 720) (by decide)
    have start : (stackPtr u).toNat - 336 = (stackPtr initial - BitVec.ofNat 64 720).toNat := by
      rw [sp, base]
      omega
    have size : (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336) = 344 := by
      rw [sp]
      omega
    change (⟨(stackPtr u).toNat - 336,
      (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)⟩ : MemoryRegion) = _
    rw [size, start]
  refine ⟨t, working, ?_, ?_, abi, ?_⟩
  · rw [result.rip, ret]
  · simpa only [pointer] using result.hashWords
  · simpa only [stackRegion, registerRegion, pointer] using frame

set_option maxHeartbeats 800000 in
theorem compress_padding [Bindings] (last : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {key chunk : ByteArray}
    {hash : Array UInt32} (ctx : Context initial boundary key)
    (state : Working initial boundary s)
    (rip : s.RIP = if last then 0x1165c4 else 0x1164fa)
    (rdi : s.regValue .rdi = rspOf s + 128)
    (rsi : s.regValue .rsi = rspOf s + 168) (rdx : s.regValue .rdx = 1)
    (hashWords : HashStateAt s (rspOf s + 128) hash)
    (bytes : (⟨(rspOf s + 168).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, Working initial boundary t ∧ t.RIP = (if last then 0x1165c9 else 0x1164ff) ∧
      HashStateAt t (rspOf t + 128)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits chunk)) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t
        #v[⟨(rspOf s + 128).toNat, 32⟩,
          ⟨(stackPtr initial - BitVec.ofNat 64 720).toNat, 344⟩] := by
  have output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 248 := by
    rw [rdi, stack_address state.rsp]
    rfl
  have input : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 208 := by
    rw [rsi, stack_address state.rsp]
    rfl
  have inputBytes : (⟨(stackPtr initial - BitVec.ofNat 64 208).toNat, 64⟩ : MemoryRegion).HasBytes
      s.external chunk := by
    simpa only [stack_address state.rsp, BitVec.reduceSub] using bytes
  obtain ⟨t, working, ripT, words, abi, frame⟩ := compression_call ctx state
    (count := 1) (if last then 0x165c4 else 0x164fa)
    (if last then 0xffff2ff7 else 0xffff30c1) 248
    (by cases last <;> decide) (by cases last <;> decide +kernel)
    (by cases last <;> decide +kernel) (by cases last <;> exact rip) output
    (by decide) (by decide) (by decide) (by rw [rdi]; exact hashWords) rdx (by
      intro u runningU call ret
      have push : pushAddr s = stackPtr initial - 384 := by
        change stackPtr s - 8 = _
        rw [state.rsp]
        simp only [blockAddress, BitVec.sub_sub]
        rfl
      have rspU : stackPtr u = stackPtr initial - 384 := call.writes.1.trans push
      have outputU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 248 :=
        (call.agrees.read (n := 64) (r := 7)
          (by simp [callEffect, pushEffect_components])).trans output
      have inputU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 208 :=
        (call.agrees.read (n := 64) (r := 6)
          (by simp [callEffect, pushEffect_components])).trans input
      let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 64 32 336 :=
        ⟨384, 208, 248, by decide, by decide, by decide, by decide,
          by decide, by decide, .inr (by decide)⟩
      have pre := callee_pre_of_stack ctx.stride ctx.stack
        (ctx.avoids (Stack.region initial stackBytes) (by simp)) ctx.outerBoundary
        runningU.machine runningU.directionFlag runningU.loaded runningU.allocated layout
        call.rip rspU inputU outputU (by
          rw [ret]
          cases last
          · exact inProgram_of_textOffset 0x164ff (by decide)
          · exact inProgram_of_textOffset 0x165c9 (by decide))
      refine ⟨pre, ?_⟩
      change (⟨(u.regValue .rsi).toNat, 64⟩ : MemoryRegion).HasBytes u.external chunk
      rw [inputU]
      refine ⟨inputBytes.1, fun i ↦ ?_⟩
      change u.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 208).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      apply (call.agrees.byte ?_).trans
      · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          using inputBytes.2 i
      · intro c hc covers
        simp only [callEffect, pushEffect_components, push, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        all_goals try exact covers.elim
        obtain ⟨j, hj, eq⟩ := covers
        apply OffsetsApart.ne (c₁ := -384) (len₁ := 8) (c₂ := -(BitVec.ofNat 64 208)) (len₂ := 64)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj
          (show i.val < 64 from by have hsize : chunk.size = 64 := bytes.1; omega) (by decide)
        simpa only [BitVec.sub_eq_add_neg] using eq.symm)
  have rsp : rspOf t = rspOf s := working.rsp.trans state.rsp.symm
  refine ⟨t, working, ?_, ?_, abi, ?_⟩
  · cases last <;> exact ripT
  · simpa only [rdi, rsp, compressBlocks_single hash chunk bytes.1] using words
  · simpa only [registerRegion, rdi] using frame

end Hkdf.Proofs.Key.Hash
