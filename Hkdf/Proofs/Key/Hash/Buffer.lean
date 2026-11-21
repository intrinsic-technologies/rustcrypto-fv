import Hkdf.Proofs.Key.Hash.State
import Hkdf.Proofs.Key.Hash.Copy
import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers
import Hkdf.Proofs.Common.Instructions.ByteStore

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Field (AdvanceTriple)

set_option maxHeartbeats 800000 in
theorem buffer [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : Working initial boundary s) (rip : s.RIP = 0x116413)
    (hashWords : HashStateAt s (rspOf s + 296)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash key))
    (tailPointer : s.regValue .r14 = initial.regValue .rsi +
      BitVec.ofNat 64 (64 * (key.size / 64)))
    (tailLength : s.regValue .r15 = BitVec.ofNat 64 (key.size % 64))
    (blocks : memLoad s.external (rspOf s + 328) 64 =
      BitVec.ofNat 64 (key.size / 64)) :
    ∃ t, Working initial boundary t ∧ t.RIP = 0x116442 ∧
      Common.StreamAt t (rspOf t + 64) key := by
  let setupBytes : List UInt8 :=
    [0x44,0x88,0xbc,0x24,0x27,0x01,0,0,
      0x4c,0x8d,0xa4,0x24,0xe8,0,0,0,
      0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x4c,0x89,0xfa]
  let setupEffect (s : RamState) : Effect :=
    { rip := 0x11642c
      writes := [⟨(.mem (rspOf s + 295) : Operand 8),
          (Operand.reg 15 : Operand 8).read s⟩,
        ⟨(.reg 12 : Operand 64), rspOf s + 232⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 232⟩,
        ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }
  have setupRun : AdvanceTriple boundary
      (fun s => s.RIP = 0x116413 ∧ MemWritable s (rspOf s + 295) 1 ∧
        RangeApart (rspOf s + 295) 1 0x116413 25)
      (codeRange 0x116413 setupBytes) (Effect.post setupEffect) := by
    advance_begin (show StepEffect _ _
        (storeEffect 0x116413 8 (fun s => rspOf s+295)
          (fun s => (Operand.reg 15 : Operand 8).read s)) from
      mov_m8_r8_effect_step 0x116413 0x44 (by simp [RexPrefix]) 7
        (.sib 4 none 0 (.d32 295)) (by decide) rfl rfl)
    case pre =>
      intro s h
      refine ⟨h.1,?_,?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        intro i hi j hj
        exact h.2.2 i hi j (by omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (rspOf s + 295) 1 0x116413 25
      exact h.2.2
    case next =>
      intro s h
      x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1641b (by decide))
    advance_then (show StepEffect _ _ (leaR64Effect 0x11641b 12 (.sib 4 none 0 (.d32 232))) from
      lea_r64_effect_step 0x11641b 0x4c (by simp [RexWPrefix]) 4
        (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x116413 setupBytes 8 8
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16423 (by decide))
    advance_then (show StepEffect _ _ (movR64R64Effect 0x116423 7 12) from
      mov_r64_r64_effect_step 0x116423 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x116413 setupBytes 16 3
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16426 (by decide))
    advance_then (show StepEffect _ _ (movR64R64Effect 0x116426 6 14) from
      mov_r64_r64_effect_step 0x116426 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x116413 setupBytes 19 3
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16429 (by decide))
    advance_then (show StepEffect _ _ (movR64R64Effect 0x116429 2 15) from
      mov_r64_r64_effect_step 0x116429 0x4c 0xfa (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x116413 setupBytes 22 3
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1642c (by decide))
    advance_finish [setupEffect]

  have setupCode := programText_slice (programLoaded_codeIn state.loaded) 0x16413
    setupBytes (by decide) (by decide +kernel)
  obtain ⟨setupFuel,u,runU,readyU,_,effectU⟩ := setupRun s
    (supportedMachine_readyToStep state.machine) setupCode
    ⟨rip, by
      rw [stack_address state.rsp]
      simp only [BitVec.ofNat_eq_ofNat,BitVec.reduceSub]
      exact stack_writable1 ctx state.toState (offset := 81) (by decide), by
      rw [stack_address state.rsp]
      simp only [BitVec.ofNat_eq_ofNat,BitVec.reduceSub]
      exact stack_codeApart ctx (offset := 81) (codeOffset := 0x16413) (by decide) (by decide) (by decide)⟩
  have setupFrame : AgreesExcept
      [.mem (rspOf s + 295) 1,.reg 12,.reg 7,.reg 6,.reg 2,.rip] s u := by
    simpa only [setupEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.cons_append,List.nil_append] using effectU.agrees
  have setupWrites : LocalWrites initial
      [.mem (rspOf s + 295) 1,.reg 12,.reg 7,.reg 6,.reg 2,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [stack_address state.rsp] at ha
    exact local_memory (offset := 81) (by decide) (by decide) a ha
  have avoids : ∀ region ∈ writeRegions initial, region.Avoids InProgram := by
    intro region member address contains inside
    exact ctx.avoids region (by simpa [writeRegions] using member) address contains (.inl inside)
  have runningU := state.toRunning.of_agrees runU readyU setupFrame
    (setupWrites.within ctx) avoids (by simp)
  have rspU : stackPtr u = stackPtr s := setupFrame.read (n := 64) (r := 4) (by simp)
  have setupValues := effectU.writes
  change memLoad u.external (rspOf s + 295) 8 = (Operand.reg 15 : Operand 8).read s ∧
    u.regValue .r12 = rspOf s + 232 ∧ u.regValue .rdi = rspOf s + 232 ∧
    u.regValue .rsi = s.regValue .r14 ∧ u.regValue .rdx = s.regValue .r15 at setupValues
  have push : pushAddr u = stackPtr initial - 384 := by
    rw [pushAddr,rspU,state.rsp,blockAddress,BitVec.sub_sub]
    rfl
  have writable : MemWritable u (pushAddr u) 8 := by
    rw [push]
    exact writable_of_grow
      (stack_sub_writable8 ctx.toCalleePre (offset := 384) (by decide) (by decide)) runningU.allocated
  have separate : RangeApart (pushAddr u) 8 0x11642c 6 := by
    rw [push]
    exact stack_codeApart ctx (offset := 384) (codeOffset := 0x1642c)
      (by decide) (by decide) (by decide)
  have pointer := Common.Memory.memcpy_pointer runningU.loaded
  have target : callMemPtr 0x11642c (.rip 0xeaee6) u = 0x10dd60 := pointer.2
  have callCode := programText_slice (programLoaded_codeIn runningU.loaded) 0x1642c
    (encodeCallM64 (.rip 0xeaee6)) (by decide) (by decide +kernel)
  have callWrites : WritesWithin
      (callEffect (callMemPtr 0x11642c (.rip 0xeaee6)) 0x116432 u).components
      (writeRegions initial) := by
    intro c hc a ha
    simp only [callEffect,pushEffect_components,push,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨Stack.region initial stackBytes,by simp [writeRegions],
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.stack.2.2.1
        (offset := 384) (by decide) (by decide) ha⟩
  obtain ⟨v,runningV,call,ret⟩ := runningU.call
    (call_m64_effect_step 0x11642c (.rip 0xeaee6) trivial rfl rfl) callCode
    ⟨⟨⟨effectU.rip,writable,separate⟩,by rw [target]; decide⟩,pointer.1⟩
    (by
      rw [target]
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide))) callWrites avoids
  have rspV : stackPtr v = stackPtr initial - 384 := call.writes.1.trans push
  have callFrame : AgreesExcept [.reg 4,.mem (stackPtr initial - 384) 8,.rip] u v := by
    simpa only [callEffect,pushEffect_components,push] using call.agrees
  have outputV : v.regValue .rdi = stackPtr initial - 144 := by
    have kept : v.regValue .rdi = u.regValue .rdi := callFrame.read (n := 64) (r := 7) (by simp)
    exact kept.trans (setupValues.2.2.1.trans (by rw [stack_address state.rsp]; rfl))
  have inputV : v.regValue .rsi = initial.regValue .rsi +
      BitVec.ofNat 64 (64 * (key.size / 64)) :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans
      (setupValues.2.2.2.1.trans tailPointer)
  have lengthV : v.regValue .rdx = BitVec.ofNat 64 (key.size % 64) :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans
      (setupValues.2.2.2.2.trans tailLength)
  have inputBound := ctx.inputBounded
  change (initial.regValue .rsi).toNat + key.size < 2^32 at inputBound
  have inputNat : (v.regValue .rsi).toNat =
      (initial.regValue .rsi).toNat + 64 * (key.size / 64) := by
    rw [inputV,BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have inputWithin (a : Nat)
      (ha : (registerRegion v .rsi (key.size % 64)).Contains a) :
      (registerRegion initial .rsi key.size).Contains a := by
    change (v.regValue .rsi).toNat ≤ a ∧ a < (v.regValue .rsi).toNat + key.size % 64 at ha
    change (initial.regValue .rsi).toNat ≤ a ∧ a < (initial.regValue .rsi).toNat + key.size
    rw [inputNat] at ha
    constructor <;> omega
  let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 0 (key.size % 64) 0 :=
    ⟨384,0,144,by decide,by decide,by decide,by decide,by decide,
      by have := Nat.mod_lt key.size (by decide : 0 < 64); omega,.inr (by have := Nat.mod_lt key.size (by decide : 0 < 64); omega)⟩
  have pre := callee_pre_of_stack_output ctx.stride ctx.stack
    (ctx.avoids (Stack.region initial stackBytes) (by simp)) ctx.outerBoundary
    runningV.machine runningV.directionFlag runningV.loaded runningV.allocated layout
    (call.rip.trans target) rspV outputV
    (by rw [ret]; exact inProgram_of_textOffset 0x16432 (by decide))
    (by change (v.regValue .rsi).toNat + key.size % 64 < 2^32; rw [inputNat]; omega)
    (by
      intro a ha
      exact Option.isSome_iff_exists.mp (runningV.allocated a
        (Option.isSome_iff_exists.mpr (ctx.inputAllocated a (inputWithin a.toNat ha)))))
    (by
      intro a ha hb
      exact ctx.separation ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide) a (inputWithin a ha) hb)
  obtain ⟨w,result,copied,_⟩ := Common.Memory.memcpy_correct pre lengthV
    (by have := Nat.mod_lt key.size (by decide : 0 < 64); omega)
  have within := stack_layout_within ctx.stack layout rspV outputV
  have runningW := runningV.of_callee result (by
    intro region member a ha
    exact ⟨Stack.region initial stackBytes,by simp [writeRegions],within region member a ha⟩)
  have pushWithin : WritesWithin
      (callEffect (callMemPtr 0x11642c (.rip 0xeaee6)) 0x116432 u).components
      #v[registerRegion v .rdi (key.size % 64),Stack.region v 0] := by
    intro c hc a ha
    simp only [callEffect,pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨Stack.region v 0,by simp,?_⟩
    rw [show pushAddr u = stackPtr v from call.writes.1.symm] at ha
    obtain ⟨i,hi,rfl⟩ := ha
    exact Hkdf.Proofs.Common.Machine.memoryRegion_contains_add pre.stack.1
      (len := 8) (by change (stackPtr v).toNat - 0 ≤ (stackPtr v).toNat; omega)
      (by rw [Hkdf.Proofs.Common.Machine.stack_region_end]; exact Nat.le_refl _) hi
  have frame := memoryWriteFrame_trans (call.agrees.memoryWriteFrame pushWithin) result.frame
  have bounds := stack_bounds ctx.toCalleePre
  have bounded (offset len : Nat) (low : offset ≤ 720) (high : len ≤ offset + 8) :
      (stackPtr initial - BitVec.ofNat 64 offset).toNat + len ≤ 2^64 := by
    rw [stack_sub_toNat ctx.toCalleePre low]
    omega
  have sameSaved := frame_agrees_of_disjoint frame (bounded 40 48 (by decide) (by decide))
    (stack_layout_disjoint ctx.stack layout rspV outputV
      (savedOffset := 40) (savedBytes := 48) (.inl (by change _ ≤ 144; omega))
      (by change 40+8 ≤ 384; decide))
  have sourceSame := frame_agrees_of_disjoint frame (bounded 81 41 (by decide) (by decide))
    (stack_layout_disjoint ctx.stack layout rspV outputV
      (savedOffset := 81) (savedBytes := 41) (.inl (by change _ ≤ 144; omega))
      (by change 81+8 ≤ 384; decide))
  have zeroU : (⟨(blockAddress initial).toNat,64⟩ : MemoryRegion).HasBytes
      u.external ⟨Array.replicate 64 0⟩ := by
    refine ⟨state.zeroBlock.1,?_⟩
    intro i
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    apply (setupFrame.byte ?_).trans
    · simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using state.zeroBlock.2 i
    · intro c hc cover
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      rw [show rspOf s = blockAddress initial from state.rsp] at cover
      obtain ⟨j,hj,he⟩ := cover
      exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 295) (len₂ := 1)
        (by unfold OffsetsApart; decide +kernel) (blockAddress initial)
        (by simpa only [ByteArray.size,Array.size_replicate] using i.isLt) hj (by decide)
        (by simpa using he)
  have zeroW := frame_hasBytes frame
    (stack_layout_disjoint ctx.stack layout rspV outputV (savedOffset := 376) (savedBytes := 64)
      (.inr (by change 144+64 ≤ 376; decide)) (by change 376+8 ≤ 384; decide))
    (bounded 376 64 (by decide) (by decide)) zeroU
  have rspW : stackPtr w = stackPtr s := by
    rw [show stackPtr w = (returnBoundary v).rsp from result.rsp,ret]
    exact rspU
  have workingW := state.of_observations runningW
    (fun i hi => (sameSaved i hi).trans (setupFrame.memory _
      (fun c hc => setupWrites.saved c hc _ ⟨i,hi,rfl⟩))) rspW
    ((result.abi.1 .rbx (by simp)).trans ((callFrame.read (n := 64) (r := 3) (by simp)).trans
      (setupFrame.read (n := 64) (r := 3) (by simp))))
    ((result.abi.1 .rbp (by simp)).trans ((callFrame.read (n := 64) (r := 5) (by simp)).trans
      (setupFrame.read (n := 64) (r := 5) (by simp))))
    (result.abi.2.2.1.trans ((callFrame.mxcsr (by simp)).trans (setupFrame.mxcsr (by simp))))
    (result.abi.2.2.2.trans ((callFrame.fcw (by simp)).trans (setupFrame.fcw (by simp)))) zeroW
  have sourcePointerW : w.regValue .r12 = rspOf w + 232 := by
    have kept : v.regValue .r12 = u.regValue .r12 := callFrame.read (n := 64) (r := 12) (by simp)
    exact (result.abi.1 .r12 (by simp)).trans
      (kept.trans (setupValues.2.1.trans (by rw [show rspOf w = rspOf s from rspW])))
  have originalBytes : (registerRegion initial .rsi key.size).HasBytes v.external key := by
    apply frame_hasBytes runningV.frame ?_
      (by change (initial.regValue .rsi).toNat + key.size ≤ 2^64; omega) ctx.bytes
    intro region member
    have cases : region = registerRegion initial .rdi 64 ∨ region = Stack.region initial stackBytes := by
      simpa [writeRegions] using member
    rcases cases with rfl | rfl
    · exact ctx.separation ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide)
    · exact ctx.separation ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide)
  have highSame : (Component.mem (rspOf s + 296) 40).Agrees s u := by
    intro i hi
    apply setupFrame.byte
    intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j,hj,he⟩ := cover
    exact OffsetsApart.ne (c₁ := 296) (len₁ := 40) (c₂ := 295) (len₂ := 1)
      (by unfold OffsetsApart; decide +kernel) (rspOf s) hi hj (by decide) he
  have sourceU : rspOf s + 295 = stackPtr initial - 81 := by
    rw [stack_address state.rsp]
    rfl
  have sourceSame' : (Component.mem (rspOf s+295) 41).Agrees u w := by
    rw [sourceU]
    exact sourceSame
  have hashW : HashStateAt w (rspOf w + 296)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash key) := by
    rw [show rspOf w = rspOf s from rspW]
    apply Hkdf.Proofs.Common.hashState_of_bytes hashWords
    intro i hi
    have same := sourceSame' (1+i) (by omega)
    have fromU := highSame i (by omega)
    have same' : w.external[rspOf s+296+BitVec.ofNat 64 i]? =
        u.external[rspOf s+296+BitVec.ofNat 64 i]? := by
      have address : rspOf s+295+BitVec.ofNat 64 (1+i) =
          rspOf s+296+BitVec.ofNat 64 i := by
        rw [BitVec.ofNat_add,BitVec.add_assoc,← BitVec.add_assoc (295 : BitVec 64),
          ← BitVec.add_assoc]
        rfl
      rw [address] at same
      exact same
    exact same'.trans fromU
  have lengthU : u.external[rspOf s + 295]? = some (UInt8.ofNat (key.size % 64)) := by
    have read := readable_of_grow
      (stack_sub_readable ctx.toCalleePre (offset := 81) (len := 1) (by decide) (by decide)) runningU.allocated
    change MemReadable u (stackPtr initial - 81) 1 at read
    rw [← sourceU] at read
    have bytes := Bytes.of_memLoad (n := 8) read.mem
    rw [setupValues.1] at bytes
    have byte := bytes 0 (by decide)
    simp only [BitVec.add_zero] at byte
    change u.external[rspOf s+295]? = some (storedByte ((s.regValue .r15).setWidth 8) 0) at byte
    rw [tailLength] at byte
    have value : storedByte ((BitVec.ofNat 64 (key.size%64)).setWidth 8) 0 =
        UInt8.ofNat (key.size%64) := by
      simp only [storedByte,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mul_zero,Nat.shiftRight_zero]
      congr 1
      omega
    exact byte.trans (congrArg some value)
  have streamW : Common.StreamAt w (rspOf w + 232) key := by
    refine ⟨?_,⟨?_,?_⟩,?_,?_⟩
    · change HashStateAt w ((rspOf w+232)+64) _
      rw [BitVec.add_assoc]
      exact hashW
    · change (key.extract (64*(key.size/64)) key.size).size = key.size%64
      rw [ByteArray.size_extract]
      omega
    · intro i
      have hi : i.val < key.size%64 := by
        have h := i.isLt
        simp only [ByteArray.size_extract] at h
        omega
      have byte := copied i.val hi
      rw [outputV,inputV] at byte
      have original := originalBytes.2 ⟨64*(key.size/64)+i.val,by omega⟩
      have dest : BitVec.ofNat 64 ((rspOf w+232).toNat+i.val) =
          stackPtr initial-144+BitVec.ofNat 64 i.val := by
        rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
          show rspOf w = rspOf s from rspW,stack_address state.rsp]
        rfl
      rw [dest]
      refine byte.trans ?_
      simpa only [registerRegion,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
        BitVec.add_assoc,ByteArray.getElem_extract] using original
    · have same := sourceSame' 0 (by decide)
      simp only [BitVec.add_zero] at same
      rw [show rspOf w = rspOf s from rspW,BitVec.add_assoc]
      exact same.trans lengthU
    · have same := agrees_memLoad_offset (offset := 33) (width := 64) sourceSame' (by decide)
      have word := agrees_memLoad_offset (offset := 32) (width := 64) highSame (by decide)
      simp only [BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] at same word
      have count : memLoad w.external (rspOf s+328) 64 = BitVec.ofNat 64 (key.size/64) :=
        same.trans (word.trans blocks)
      have read := readable_of_grow
        (stack_sub_readable ctx.toCalleePre (offset := 48) (len := 8) (by decide) (by decide)) runningW.allocated
      have address : rspOf s+328 = stackPtr initial-48 := by rw [stack_address state.rsp]; rfl
      change MemReadable w (stackPtr initial-48) 8 at read
      rw [← address] at read
      have bytes := Bytes.of_memLoad (n := 64) read.mem
      rw [count] at bytes
      rw [show rspOf w = rspOf s from rspW,BitVec.add_assoc]
      exact bytes.loadBytes64
  have copyPre : Copy.Pre w := by
    refine ⟨?_,runningW.directionFlag.df,sourcePointerW,?_,?_,?_,?_⟩
    · rw [result.rip,ret]
      rfl
    · rw [stack_address workingW.rsp]
      simp only [BitVec.ofNat_eq_ofNat,BitVec.reduceSub]
      exact stack_readable ctx workingW.toState (by decide) (by decide)
    · rw [stack_address workingW.rsp]
      have read := stack_readable ctx workingW.toState (offset := 312) (len := 104) (by decide) (by decide)
      refine ⟨read,tables_of_not_reserved (by decide) read.low ?_⟩
      intro i hi reserved
      exact ctx.avoids (Stack.region initial stackBytes) (by simp)
        (stackPtr initial-312+BitVec.ofNat 64 i)
        (Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.stack.2.2.1
          (offset := 312) (by decide) (by decide) ⟨i,hi,rfl⟩) (.inr reserved)
    · rw [stack_address workingW.rsp,stack_address workingW.rsp]
      simp only [BitVec.ofNat_eq_ofNat,BitVec.reduceSub]
      rw [stack_sub_toNat ctx.toCalleePre (offset := 312) (by decide),
        stack_sub_toNat ctx.toCalleePre (offset := 144) (by decide)]
      have low : 720 ≤ (stackPtr initial).toNat := ctx.stack.2.2.1
      omega
    · rw [stack_address workingW.rsp]
      exact stack_codeApart ctx (offset := 312) (codeOffset := 0x1643f)
        (by decide) (by decide) (by decide)
  obtain ⟨copyFuel,t,copyRun,copyReady,copyRip,copyFrame,copyBytes⟩ :=
    Copy.run ctx.stride ctx.outerBoundary (supportedMachine_readyToStep runningW.machine)
      runningW.loaded copyPre
  have copyWrites : LocalWrites initial
      [.reg 1,.reg 6,.reg 7,.mem (rspOf w+64) 104,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [stack_address workingW.rsp] at ha
    exact local_memory (offset := 312) (by decide) (by decide) a ha
  have runningT := runningW.of_agrees copyRun copyReady copyFrame
    (copyWrites.within ctx) avoids (by simp)
  have zeroT : (⟨(blockAddress initial).toNat,64⟩ : MemoryRegion).HasBytes
      t.external ⟨Array.replicate 64 0⟩ := by
    refine ⟨workingW.zeroBlock.1,?_⟩
    intro i
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    apply (copyFrame.byte ?_).trans
    · simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using workingW.zeroBlock.2 i
    · intro c hc cover
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      rw [show rspOf w = blockAddress initial from workingW.rsp] at cover
      obtain ⟨j,hj,he⟩ := cover
      exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 64) (len₂ := 104)
        (by unfold OffsetsApart; decide +kernel) (blockAddress initial)
        (by simpa only [ByteArray.size,Array.size_replicate] using i.isLt) hj (by decide)
        (by simpa using he)
  have rspT : stackPtr t = stackPtr w := copyFrame.read (n := 64) (r := 4) (by simp)
  have workingT := workingW.of_observations runningT
    (fun i hi => copyFrame.memory _ (fun c hc => copyWrites.saved c hc _ ⟨i,hi,rfl⟩)) rspT
    (copyFrame.read (n := 64) (r := 3) (by simp))
    (copyFrame.read (n := 64) (r := 5) (by simp))
    (copyFrame.mxcsr (by simp)) (copyFrame.fcw (by simp)) zeroT
  refine ⟨t,workingT,copyRip,?_⟩
  rw [show rspOf t = rspOf w from rspT]
  exact Common.StreamAt.of_copy streamW copyBytes

end Hkdf.Proofs.Key.Hash
