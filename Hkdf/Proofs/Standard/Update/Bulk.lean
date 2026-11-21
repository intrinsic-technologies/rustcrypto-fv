import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Standard.Update.State
import Hkdf.Proofs.Standard.Initialization.Inner
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Standard.Update.Blocks
import Hkdf.Proofs.Standard.Update.Short
import Hkdf.Proofs.Wrapper.Absorb.Mathematics

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Standard.Initialization

theorem compress_input [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input} {hash : Array UInt32}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : Preserved initial s) (i : Fin inputs.size) (offset count : Nat)
    (bound : offset + 64 * count ≤ inputs[i].bytes.size)
    (rip : s.RIP = 0x1016d5)
    (source : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (output : s.regValue .rdi = frameBase initial + 184)
    (blocks : s.regValue .rdx = BitVec.ofNat 64 count)
    (words : HashStateAt s (frameBase initial + 184) hash) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Preserved initial t ∧ t.RIP = 0x1016da ∧
      HashStateAt t (frameBase initial + 184)
        (compressBlocks hash (inputs[i].bytes.extract offset (offset + 64 * count))) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t (innerWriteRegions initial 32 336) := by
  obtain ⟨v, callRun, readyV, runningV, called, callFrame, rspV, retV⟩ :=
    hash_call ctx state ready rip
      (call_rel32_effect_step 0x1016d5 0x7ee6 (by decide))
      (programText_slice (programLoaded_codeIn state.loaded) 0x16d5 _
        (by decide) (by decide +kernel))
      (Standard.stack_codeApart ctx (codeOffset := 0x16d5) (by decide) (by decide) (by decide))
  have outputAddress : frameBase initial + 184 = stackPtr initial - BitVec.ofNat 64 336 := by
    have h := Standard.stack_address state.rsp (offset := 184) (by decide)
    rw [show rspOf s = frameBase initial from state.rsp] at h
    exact h
  have outputV : v.regValue .rdi = stackPtr initial - BitVec.ofNat 64 336 :=
    ((called.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans output).trans outputAddress
  have sourceV : v.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset :=
    (called.agrees.read (n := 64) (r := 6)
      (by simp [callEffect, pushEffect_components])).trans source
  have countV : v.regValue .rdx = BitVec.ofNat 64 count :=
    (called.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans blocks
  obtain ⟨inputV, apartV⟩ := extract_input_slice ctx.call runningV.frame i bound
  let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout hkdfSha256Extract.minStackBytes 0 32 336 :=
    ⟨528, 0, 336, by decide, by decide, by decide, by decide, by decide,
      by decide, .inr (by decide)⟩
  have callee := callee_pre_of_stack_output ctx.environment.stringStride ctx.call.stack
    (ctx.call.stackSeparation.2 _ (by simp)).2 (returnBoundary_valid ctx).2.2
    runningV.machine runningV.directionFlag runningV.loaded runningV.allocated layout
    called.rip rspV outputV
    (by rw [retV]; exact inProgram_of_textOffset 0x16da (by decide))
    (by change (v.regValue .rsi).toNat + 64 * count < 2^32; rw [sourceV]; exact inputV.1)
    (by
      intro a ha
      change (v.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (v.regValue .rsi).toNat + 64 * count at ha
      rw [sourceV] at ha
      let start := (inputs[i].address + BitVec.ofNat 64 offset).toNat
      have size : (inputs[i].bytes.extract offset (offset + 64 * count)).size = 64 * count := inputV.2.1
      have index : a.toNat - start < (inputs[i].bytes.extract offset (offset + 64 * count)).size := by
        rw [size]
        change start ≤ a.toNat ∧ a.toNat < start + 64 * count at ha
        omega
      have byte := inputV.2.2 ⟨a.toNat - start, index⟩
      have addr : start + (a.toNat - start) = a.toNat := by
        change start ≤ a.toNat ∧ _ at ha
        omega
      change v.external[BitVec.ofNat 64 (start + (a.toNat - start))]? = _ at byte
      rw [addr, BitVec.ofNat_toNat] at byte
      exact ⟨_, byte⟩)
    (by change (⟨(v.regValue .rsi).toNat, 64 * count⟩ : MemoryRegion).Disjoint _
        rw [sourceV]; exact apartV)
  have hashV : HashStateAt v (stackPtr initial - BitVec.ofNat 64 336) hash := by
    rw [← outputAddress]
    apply Hkdf.Proofs.Wrapper.hashState_of_bytes words
    rw [outputAddress]
    exact inner_frame_agrees ctx callFrame (offset := 336) (len := 32)
      (by decide) (by decide) (by decide) (by decide)
  have pre : Common.SHA256.CompressionPre v (returnBoundary initial) hash
      (inputs[i].bytes.extract offset (offset + 64 * count)) count := by
    refine ⟨callee, ?_, countV, ?_, ?_⟩
    · rw [outputV, Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 336) (by decide)]
      have aligned : (stackPtr initial).toNat % 16 = 8 := ctx.call.stack.2.2.2
      have bounds := Standard.stack_bounds ctx
      omega
    · change (⟨(v.regValue .rsi).toNat, 64 * count⟩ : MemoryRegion).HasBytes _ _
      rw [sourceV]
      exact inputV.2
    · rw [outputV]
      exact hashV
  obtain ⟨t, result⟩ := Common.SHA256.compression_correct pre
  have resultFrame := hash_compression_frame ctx (by decide) rspV outputV result.frame
  have fullFrame := memoryWriteFrame_trans (hash_zero_frame callFrame) resultFrame
  have runningT := runningV.of_callee result.toCalleeResult
    (by intro region member a contains
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          stack_layout_within ctx.call.stack layout rspV outputV region member a contains⟩)
  have rspT : t.regValue .rsp = frameBase initial := by rw [result.rsp, retV]
  have stateT := inner_preserved_of_frame ctx state runningT fullFrame rspT
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1 + fuel, t, callRun.trans run, supportedMachine_readyToStep result.machine,
    stateT, ?_, ?_, (call_result callee called result.toCalleeResult state.directionFlag).2,
    fullFrame⟩
  · rw [result.rip, retV]
    rfl
  · rw [outputAddress]
    simpa only [outputV] using result.hashWords

theorem effect_preserved [Bindings] {initial s t : RamState} {fuel hashBytes hashOffset : Nat}
    {salt : Option ByteArray} {inputs : Array Input} {effect : Effect}
    (ctx : Context initial salt inputs) (state : Preserved initial s)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (holds : effect.Holds s t)
    (writes : WritesWithin effect.components (innerWriteRegions initial hashBytes hashOffset))
    (bounds : hashOffset ≤ 504 ∧ 48 + hashBytes ≤ hashOffset ∧
      (hashOffset ≤ 400 ∨ 424 + hashBytes ≤ hashOffset))
    (rsp : .reg 4 ∉ effect.components) (df : .df ∉ effect.components) :
    Preserved initial t ∧ MemoryWriteFrame s t (innerWriteRegions initial hashBytes hashOffset) := by
  have frame := holds.agrees.memoryWriteFrame writes
  have running := state.toRunning.of_agrees run ready holds.agrees
    (by intro c hc a ha
        obtain ⟨region, member, contains⟩ := writes c hc a ha
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          hash_write_regions_within ctx (by omega) region member a.toNat contains⟩)
    (by intro region member a contains inside
        exact (ctx.call.stackSeparation.2 region (by simpa using member)).2 a contains (.inl inside)) df
  exact ⟨inner_preserved_of_frame ctx state running frame
    ((holds.agrees.read (n := 64) (r := 4) rsp).trans state.rsp) bounds, frame⟩

theorem bulk_count [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (state : Preserved initial s)
    (rip : s.RIP = 0x1016c2) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Preserved initial t ∧ (bulkEffect s).Holds s t ∧
      MemoryWriteFrame s t (innerWriteRegions initial 40 336) := by
  have writable : MemWritable s (rspOf s + 216) 8 := by
    change MemWritable s (rspOf s + BitVec.ofNat 64 216) 8
    rw [Standard.stack_address state.rsp (by decide)]
    exact CallFrame.stack_writable8 ctx.call.stack
      (ctx.call.stackSeparation.2 _ (by simp)).2 state.allocated (by decide) (by decide)
  have apart : RangeApart (rspOf s + 216) 8 0x1016c2 19 := by
    change RangeApart (rspOf s + BitVec.ofNat 64 216) 8 _ _
    rw [Standard.stack_address state.rsp (by decide)]
    exact Standard.stack_codeApart ctx (codeOffset := 0x16c2) (by decide) (by decide) (by decide)
  obtain ⟨fuel, t, run, readyT, _, effect⟩ := bulk_setup
    (returnBoundary initial) (returnBoundary_valid ctx).2.2 s
    (supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) 0x16c2 bulkBytes
      (by decide) (by decide +kernel)) ⟨rip, writable, apart⟩
  have writes : WritesWithin (bulkEffect s).components (innerWriteRegions initial 40 336) := by
    intro c hc a ha
    simp only [bulkEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 336).toNat, 40⟩,
      by simp [innerWriteRegions],
      hash_output_memory ctx state (by decide) (by decide) (by decide) ha⟩
  have result := effect_preserved ctx state run readyT effect writes (by decide)
    (by simp [bulkEffect, Effect.components, Write.component, Operand.component])
    (by simp [bulkEffect, Effect.components, Write.component, Operand.component])
  exact ⟨fuel, t, run, readyT, result.1, effect, result.2⟩

theorem append_prefix_slice (a b : ByteArray) (offset count : Nat) :
    (a ++ b.extract 0 offset) ++ b.extract offset (offset + count) =
      a ++ b.extract 0 (offset + count) := by
  rw [ByteArray.append_assoc, ByteArray.extract_append_extract]
  simp only [Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (by omega : offset ≤ offset + count)]

structure BulkTail [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) (i : Fin inputs.size) (consumed : Nat) : Prop extends
    Buffered initial s salt (prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0
      (consumed + 64 * ((inputs[i].bytes.size - consumed) / 64))) where
  consumedBound : consumed ≤ inputs[i].bytes.size
  aligned : (prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 consumed).size % 64 = 0
  rip : s.RIP = 0x1016da
  pointer : s.regValue .r13 = inputs[i].address + BitVec.ofNat 64 consumed
  length : s.regValue .rbp = BitVec.ofNat 64 (inputs[i].bytes.size - consumed)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 i.val
  copyRegister : s.regValue .r12 = 0x10dd60

theorem bulk_blocks [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {i : Fin inputs.size} {consumed : Nat} {direct : Bool}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : BulkInput initial s salt inputs i consumed direct) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      BulkTail initial t salt inputs i consumed := by
  let count := (inputs[i].bytes.size - consumed) / 64
  let before := prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 consumed
  let after := prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 (consumed + 64 * count)
  let pad := HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36
  have inputBound := extract_input_bound ctx.call i
  have leftBound := state.consumedBound
  have sizeBefore : before.size = (prefixConcatenation inputs i.val).size + consumed := by
    simp only [before, ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left leftBound, Nat.sub_zero]
  have fullBound : consumed + 64 * count ≤ inputs[i].bytes.size := by dsimp only [count]; omega
  have sizeAfter : after.size = before.size + 64 * count := by
    simp only [after, ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left fullBound, Nat.sub_zero, sizeBefore]
    omega
  have alignedBefore : before.size % 64 = 0 := state.aligned
  have alignedAfter : after.size % 64 = 0 := by rw [sizeAfter]; omega
  have sizePad : pad.size = 64 := HMAC.xorPad_keyBlock_size _ _
  have innerAligned : (pad ++ before).size % 64 = 0 := by
    rw [ByteArray.size_append, sizePad]
    omega
  have messageEq : (pad ++ before) ++ inputs[i].bytes.extract consumed (consumed + 64 * count) =
      pad ++ after := by
    rw [ByteArray.append_assoc, append_prefix_slice]
  have hashEq : compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ after) =
      compressBlocks (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ before))
        (inputs[i].bytes.extract consumed (consumed + 64 * count)) := by
    rw [← messageEq, compressBlocks_append _ _ _ innerAligned]
  have countEq : (pad ++ after).size / 64 = (pad ++ before).size / 64 + count := by
    simp only [ByteArray.size_append, sizePad, sizeAfter]
    omega
  have lengthNat : (s.regValue .rbp).toNat = inputs[i].bytes.size - consumed := by
    rw [state.length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨selectFuel, u, selectRun, readyU, ripU, countU, selectFrame⟩ :=
    select_blocks ready state.loaded (returnBoundary_valid ctx).2.2 direct state.rip
  rw [lengthNat] at ripU countU
  change u.RIP = (if count = 0 then 0x1016da else 0x1016c2) at ripU
  change u.regValue .rdx = BitVec.ofNat 64 count at countU
  have bufferedU := buffered_of_noMem ctx state.toBuffered selectRun readyU selectFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  have pointerU := (selectFrame.read (n := 64) (r := 13) (by simp)).trans state.pointer
  have lengthU := (selectFrame.read (n := 64) (r := 5) (by simp)).trans state.length
  have indexU := (selectFrame.read (n := 64) (r := 14) (by simp)).trans state.indexRegister
  have copyU := (selectFrame.read (n := 64) (r := 12) (by simp)).trans state.copyRegister
  by_cases zero : count = 0
  · refine ⟨selectFuel, u, selectRun, readyU, ?_⟩
    refine ⟨?_, state.consumedBound, state.aligned, by simpa only [zero, ↓reduceIte] using ripU, pointerU, lengthU, indexU, copyU⟩
    change Buffered initial u salt (prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 (consumed + 64 * count))
    simpa only [zero, Nat.mul_zero, Nat.add_zero] using bufferedU
  · obtain ⟨setupFuel, v, setupRun, readyV, preservedV, setup, setupFrame⟩ :=
      bulk_count ctx bufferedU.toPreserved (by simpa only [zero, ↓reduceIte] using ripU)
    have setupWrites := setup.writes
    change memLoad v.external (rspOf u + 216) 64 =
        memLoad u.external (rspOf u + 216) 64 + u.regValue .rdx ∧
      v.regValue .rdi = rspOf u + 184 ∧ v.regValue .rsi = u.regValue .r13 at setupWrites
    have spU : rspOf u = frameBase initial := bufferedU.rsp
    have outputV : v.regValue .rdi = frameBase initial + 184 := by rw [setupWrites.2.1, spU]
    have sourceV := setupWrites.2.2.trans pointerU
    have countV : v.regValue .rdx = BitVec.ofNat 64 count :=
      (setup.agrees.read (n := 64) (r := 2)
        (by simp [bulkEffect, Effect.components, Write.component, Operand.component])).trans countU
    have wordsU : HashStateAt u (frameBase initial + 184)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ before)) := by
      simpa only [pad, before, hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using bufferedU.hmac.inner.hashWords
    have hashAddress : frameBase initial + 184 = stackPtr initial - BitVec.ofNat 64 336 := by
      have addr := Standard.stack_address bufferedU.rsp (offset := 184) (by decide)
      rw [spU] at addr
      exact addr
    have wordsV : HashStateAt v (frameBase initial + 184)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ before)) := by
      apply Hkdf.Proofs.Wrapper.hashState_of_bytes wordsU
      rw [hashAddress]
      intro j hj
      apply setup.agrees.memory
      intro c hc cover
      simp only [bulkEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
        Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      obtain ⟨k, hk, equal⟩ := cover
      have addr := Standard.stack_address bufferedU.rsp (offset := 216) (by decide)
      change stackPtr initial - BitVec.ofNat 64 336 + BitVec.ofNat 64 j =
        rspOf u + BitVec.ofNat 64 216 + BitVec.ofNat 64 k at equal
      rw [addr] at equal
      exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel :
        OffsetsApart (-336) 32 (-304) 8) (stackPtr initial) hj hk (by decide)
        (by simpa only [BitVec.sub_eq_add_neg, Nat.reduceSub, BitVec.ofNat_eq_ofNat] using equal)
    obtain ⟨compressionFuel, t, compressionRun, readyT, preservedT, ripT, wordsT, abi, compressionFrame⟩ :=
      compress_input ctx readyV preservedV i consumed count fullBound setup.rip sourceV outputV countV wordsV
    have laterFrame := memoryWriteFrame_trans setupFrame (inner_frame_mono compressionFrame (by decide : 32 ≤ 40))
    have pointerT : t.regValue .r13 = inputs[i].address + BitVec.ofNat 64 consumed :=
      (abi.1 .r13 (by simp)).trans ((setup.agrees.read (n := 64) (r := 13)
        (by simp [bulkEffect, Effect.components, Write.component, Operand.component])).trans pointerU)
    have lengthT : t.regValue .rbp = BitVec.ofNat 64 (inputs[i].bytes.size - consumed) :=
      (abi.1 .rbp (by simp)).trans ((setup.agrees.read (n := 64) (r := 5)
        (by simp [bulkEffect, Effect.components, Write.component, Operand.component])).trans lengthU)
    have indexT := (abi.1 .r14 (by simp)).trans ((setup.agrees.read (n := 64) (r := 14)
      (by simp [bulkEffect, Effect.components, Write.component, Operand.component])).trans indexU)
    have copyT := (abi.1 .r12 (by simp)).trans ((setup.agrees.read (n := 64) (r := 12)
      (by simp [bulkEffect, Effect.components, Write.component, Operand.component])).trans copyU)
    have countAddress : frameBase initial + 216 = stackPtr initial - BitVec.ofNat 64 304 := by
      have addr := Standard.stack_address bufferedU.rsp (offset := 216) (by decide)
      rw [spU] at addr
      exact addr
    have oldWord : memLoad u.external (frameBase initial + 216) 64 =
        BitVec.ofNat 64 ((pad ++ before).size / 64) := by
      have h := Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64 bufferedU.hmac.inner.blocks
      simpa only [pad, before, hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    have wordV : memLoad v.external (frameBase initial + 216) 64 =
        BitVec.ofNat 64 ((pad ++ after).size / 64) := by
      rw [spU, oldWord, countU, ← BitVec.ofNat_add, ← countEq] at setupWrites
      exact setupWrites.1
    have wordT : memLoad t.external (frameBase initial + 216) 64 =
        BitVec.ofNat 64 ((pad ++ after).size / 64) := by
      rw [countAddress] at wordV ⊢
      exact (CallFrame.agrees_memLoad (inner_frame_agrees ctx compressionFrame
        (offset := 304) (len := 8) (by decide) (by decide) (by decide) (by decide))).trans wordV
    have countBytes : Machine.loadBytes t.external (frameBase initial + 216) 8 =
        .ok (BitVec.ofNat 64 ((pad ++ after).size / 64)) := by
      rw [countAddress] at wordT ⊢
      have bytes := Bytes.of_memLoad (n := 64)
        (Standard.stack_readable ctx preservedT.toState (offset := 304) (len := 8) (by decide) (by decide)).mem
      rw [wordT] at bytes
      exact bytes.loadBytes64
    have newAligned : (pad ++ after).size % 64 = 0 := by
      rw [ByteArray.size_append, sizePad]
      omega
    have emptyTail : (pad ++ after).extract (64 * ((pad ++ after).size / 64))
        (pad ++ after).size = ByteArray.empty := by
      rw [show 64 * ((pad ++ after).size / 64) = (pad ++ after).size by omega,
        ByteArray.extract_same]
    have tailLength : t.external[hmacBase initial + 63]? = some (UInt8.ofNat 0) := by
      have old := bufferedU.hmac.inner.tailLength
      change u.external[hmacBase initial + 63]? = some (UInt8.ofNat ((pad ++ before).size % 64)) at old
      rw [innerAligned] at old
      have addr : hmacBase initial + 63 = stackPtr initial - BitVec.ofNat 64 337 := by
        change stackPtr initial - 520 + 120 + 63 = _
        bv_omega
      rw [addr] at old ⊢
      have same := inner_frame_agrees ctx laterFrame (offset := 337) (len := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)
      simpa only [BitVec.add_zero] using same.trans (by simpa only [BitVec.add_zero] using old)
    have outerAddress : hmacBase initial + 104 = stackPtr initial - BitVec.ofNat 64 296 := by
      change stackPtr initial - 520 + 120 + 104 = _
      bv_omega
    have outerHash : HashStateAt t (hmacBase initial + 104)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x5c)) :=
      Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedU.hmac.outerHash (by
      rw [outerAddress]
      exact inner_frame_agrees ctx laterFrame (offset := 296) (len := 32)
        (by decide) (by decide) (by decide) (by decide))
    have outerBlocks : Machine.loadBytes t.external (hmacBase initial + 136) 8 = .ok 1 := by
      have addr : hmacBase initial + 136 = stackPtr initial - BitVec.ofNat 64 264 := by
        change stackPtr initial - 520 + 120 + 136 = _
        bv_omega
      rw [addr]
      have old := bufferedU.hmac.outerBlocks
      rw [addr] at old
      exact (CallFrame.agrees_loadBytes (inner_frame_agrees ctx laterFrame
        (offset := 264) (len := 8) (by decide) (by decide) (by decide) (by decide))).trans old
    refine ⟨selectFuel + setupFuel + compressionFuel, t,
      (selectRun.trans setupRun).trans compressionRun, readyT,
      ⟨⟨preservedT, ⟨⟨?_, ?_, ?_, ?_⟩, outerHash, outerBlocks⟩⟩,
        state.consumedBound, state.aligned, ripT, pointerT, lengthT, indexT, copyT⟩⟩
    · rw [← hashEq] at wordsT
      simpa only [pad, after, count, hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using wordsT
    · change (⟨(hmacBase initial).toNat, (pad ++ after).size % 64⟩ : MemoryRegion).HasBytes
        t.external ((pad ++ after).extract _ _)
      rw [newAligned, emptyTail]
      exact ⟨rfl, fun i ↦ Fin.elim0 i⟩
    · change t.external[hmacBase initial + 63]? = some (UInt8.ofNat ((pad ++ after).size % 64))
      rw [newAligned]
      exact tailLength
    · simpa only [pad, after, count, hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using countBytes


theorem bulk_tail [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {i : Fin inputs.size} {consumed : Nat}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : BulkTail initial s salt inputs i consumed) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      InputDone initial t salt inputs i.val false := by
  let remaining := inputs[i].bytes.size - consumed
  let full := consumed + 64 * (remaining / 64)
  let tail := remaining % 64
  let bytes := inputs[i].bytes.extract full (full + tail)
  let message := prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 full
  let previous := HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++ message
  have inputBound := extract_input_bound ctx.call i
  have consumedBound := state.consumedBound
  have tailBound : tail < 64 := Nat.mod_lt _ (by decide)
  have fullBound : full ≤ inputs[i].bytes.size := by dsimp only [full, remaining]; omega
  have total : full + tail = inputs[i].bytes.size := by dsimp only [full, tail, remaining]; omega
  have byteSize : bytes.size = tail := by
    simp only [bytes, ByteArray.size_extract, total, Nat.min_self]
    omega
  have messageAligned : message.size % 64 = 0 := by
    have old := state.aligned
    simp only [ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left consumedBound, Nat.sub_zero] at old
    simp only [message, ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left fullBound, Nat.sub_zero, full]
    omega
  have previousAligned : previous.size % 64 = 0 := by
    dsimp only [previous]
    rw [ByteArray.size_append, HMAC.xorPad_keyBlock_size]
    omega
  have short : bytes.size < 64 - previous.size % 64 := by rw [byteSize, previousAligned]; omega
  have counts := Hkdf.Proofs.Wrapper.Absorb.append_short_counts previous bytes short
  have messageEq : message ++ bytes = prefixConcatenation inputs (i.val + 1) := by
    rw [prefixConcatenation_succ inputs i.val i.isLt]
    change (prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 full) ++
      inputs[i].bytes.extract full (full + tail) = _
    rw [append_prefix_slice, total, ByteArray.extract_zero_size]
    rfl
  have previousEq : previous ++ bytes = HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++
      prefixConcatenation inputs (i.val + 1) := by
    change (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++ message) ++ bytes = _
    rw [ByteArray.append_assoc, messageEq]
  obtain ⟨registerFuel, a, registerRun, readyA, _, registers⟩ := tail_registers
    (returnBoundary initial) (returnBoundary_valid ctx).2.2 s ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x16da tailRegisterBytes
      (by decide) (by decide +kernel)) state.rip
  have registerFrame : AgreesExcept [.reg 0, .reg 1, .reg 5, .reg 13, .flags, .rip] s a := registers.agrees
  have bufferedA := buffered_of_noMem ctx state.toBuffered registerRun readyA registerFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  have remainingNat : (s.regValue .rbp).toNat = remaining := by
    rw [state.length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have registerWrites := registers.writes
  change a.regValue .rax = 0x7fffffffffffffc0 &&& s.regValue .rbp ∧
    a.regValue .rcx = 0x7fffffffffffffc0 ∧
    a.regValue .rbp = ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64 ∧
    a.regValue .r13 = s.regValue .r13 + (0x7fffffffffffffc0 &&& s.regValue .rbp) at registerWrites
  have lengthA : a.regValue .rbp = BitVec.ofNat 64 tail := by
    rw [registerWrites.2.2.1, Hkdf.Proofs.Wrapper.Absorb.tail_length, remainingNat]
  have pointerA : a.regValue .r13 = inputs[i].address + BitVec.ofNat 64 full := by
    rw [registerWrites.2.2.2, state.pointer, Hkdf.Proofs.Wrapper.Absorb.full_length _
      (by rw [remainingNat]; dsimp only [remaining]; omega), remainingNat,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have writable : MemWritable a (rspOf a + 183) 1 := by
    change MemWritable a (rspOf a + BitVec.ofNat 64 183) 1
    rw [Standard.stack_address bufferedA.rsp (by decide)]
    exact CallFrame.stack_writable1 ctx.call.stack
      (ctx.call.stackSeparation.2 _ (by simp)).2 bufferedA.allocated (by decide)
  have apart : RangeApart (rspOf a + 183) 1 0x1016f0 19 := by
    change RangeApart (rspOf a + BitVec.ofNat 64 183) 1 _ _
    rw [Standard.stack_address bufferedA.rsp (by decide)]
    exact Standard.stack_codeApart ctx (codeOffset := 0x16f0) (by decide) (by decide) (by decide)
  obtain ⟨setupFuel, b, setupRun, readyB, _, setup⟩ := tail_setup
    (returnBoundary initial) (returnBoundary_valid ctx).2.2 a readyA
    (programText_slice (programLoaded_codeIn bufferedA.loaded) 0x16f0 tailBytes
      (by decide) (by decide +kernel)) ⟨registers.rip, writable, apart⟩
  have writes : WritesWithin (tailEffect a).components (innerWriteRegions initial 1 337) := by
    intro c hc addr ha
    simp only [tailEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 337).toNat, 1⟩,
      by simp [innerWriteRegions], hash_output_memory ctx bufferedA.toPreserved
        (by decide) (by decide) (by decide) ha⟩
  have setupResult := effect_preserved ctx bufferedA.toPreserved setupRun readyB setup writes
    (by decide) (by simp [tailEffect, Effect.components, Write.component, Operand.component])
    (by simp [tailEffect, Effect.components, Write.component, Operand.component])
  have setupWrites := setup.writes
  change memLoad b.external (rspOf a + 183) 8 = (a.regValue .rbp).setWidth 8 ∧
    b.regValue .rdi = rspOf a + 120 ∧ b.regValue .rsi = a.regValue .r13 ∧
    b.regValue .rdx = a.regValue .rbp at setupWrites
  have destinationB : b.regValue .rdi = hmacBase initial + BitVec.ofNat 64 0 := by
    rw [setupWrites.2.1, show rspOf a = frameBase initial from bufferedA.rsp]
    simp only [hmacBase, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have copyB : b.regValue .r12 = 0x10dd60 :=
    (setup.agrees.read (n := 64) (r := 12)
      (by simp [tailEffect, Effect.components, Write.component, Operand.component])).trans
      ((registerFrame.read (n := 64) (r := 12) (by simp)).trans state.copyRegister)
  obtain ⟨copyFuel, t, copyRun, readyT, preservedT, ripT, abi, copyFrame, copied⟩ :=
    Short.copy ctx setupResult.1 .tail i (sourceOffset := full) (position := 0) (count := tail)
      (Nat.le_of_eq total) (by omega) setup.rip destinationB
      (setupWrites.2.2.1.trans pointerA) (setupWrites.2.2.2.trans lengthA) copyB
  have stored : b.external[hmacBase initial + 63]? = some (UInt8.ofNat tail) := by
    have value := setupWrites.1
    rw [lengthA, BitVec.setWidth_ofNat_of_le (by decide)] at value
    have h := Bytes.of_memLoad (n := 8)
      (fun j hj ↦ setup.agrees.grow _ (writable.mem j hj)) 0 (by decide)
    rw [value, BitVec.add_zero] at h
    have addr : rspOf a + 183 = hmacBase initial + 63 := by
      rw [show rspOf a = frameBase initial from bufferedA.rsp, hmacBase, BitVec.add_assoc]
      rfl
    rw [addr] at h
    simpa only [storedByte, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt (by omega : tail < 256)] using h
  have hmacAddress (offset : Nat) (bound : offset ≤ 400) :
      hmacBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (400 - offset) := by
    change stackPtr initial - 520 + 120 + BitVec.ofNat 64 offset = _
    have sub : (400 : BitVec 64) - BitVec.ofNat 64 offset = BitVec.ofNat 64 (400-offset) :=
      BitVec.ofNat_sub_ofNat_of_le 400 offset (by omega) bound
    rw [← sub]
    bv_omega
  have unchanged (offset len : Nat) (bound : offset + len ≤ 144) (above : 64 ≤ offset) :
      ∀ j < len, t.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
        a.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? := by
    have addr := hmacAddress offset (by omega)
    have first := inner_frame_agrees ctx setupResult.2 (offset := 400-offset) (len := len)
      (by omega) (by omega) (by omega) (by omega)
    have second := Short.copy_observation ctx copyFrame (offset := 400-offset) (len := len)
      (by omega) (by omega) (by omega) (by omega)
    rw [addr]
    exact fun j hj ↦ (second j hj).trans (first j hj)
  have storedT : t.external[hmacBase initial + 63]? = some (UInt8.ofNat tail) := by
    have observed := Short.copy_observation ctx copyFrame (offset := 337) (len := 1)
      (by omega) (by decide) (by decide) (by omega)
    have addr : hmacBase initial + 63 = stackPtr initial - BitVec.ofNat 64 337 := by
      simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using hmacAddress 63 (by decide)
    rw [addr] at stored ⊢
    have equal := observed 0 (by decide)
    simp only [BitVec.add_zero] at equal
    exact equal.trans stored
  have inner : StreamAt t (hmacBase initial) (previous ++ bytes) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Hkdf.Proofs.Wrapper.Absorb.compressBlocks_append_short _ _ _ short]
      apply Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.inner.hashWords
      intro j hj
      simpa only [BitVec.ofNat_eq_ofNat] using unchanged 64 32 (by decide) (by decide) j hj
    · change (⟨(hmacBase initial).toNat, (previous ++ bytes).size % 64⟩ : MemoryRegion).HasBytes
        t.external (remainderBytes (previous ++ bytes))
      rw [Hkdf.Proofs.Wrapper.Absorb.remainderBytes_append_aligned _ _ previousAligned,
        Hkdf.Proofs.Wrapper.Absorb.remainderBytes_short _ (by rw [byteSize]; exact tailBound),
        counts.2, previousAligned, Nat.zero_add, byteSize]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using copied
    · rw [counts.2, previousAligned, Nat.zero_add, byteSize]
      exact storedT
    · rw [counts.1]
      change Machine.loadBytes t.external (hmacBase initial + BitVec.ofNat 64 96) 8 = _
      rw [Hkdf.Proofs.Common.Memory.loadBytes_congr (fun j hj ↦ unchanged 96 8 (by decide) (by decide) j hj)]
      exact bufferedA.hmac.inner.blocks
  have hmac : HmacAt t (hmacBase initial) (saltKey salt) (prefixConcatenation inputs (i.val + 1)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [previousEq] at inner
      exact inner
    · apply Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.outerHash
      intro j hj
      simpa only [BitVec.ofNat_eq_ofNat] using unchanged 104 32 (by decide) (by decide) j hj
    · change Machine.loadBytes t.external (hmacBase initial + BitVec.ofNat 64 136) 8 = _
      rw [Hkdf.Proofs.Common.Memory.loadBytes_congr (fun j hj ↦ unchanged 136 8 (by decide) (by decide) j hj)]
      exact bufferedA.hmac.outerBlocks
  refine ⟨registerFuel + setupFuel + copyFuel, t, (registerRun.trans setupRun).trans copyRun, readyT, {
    toBuffered := ⟨preservedT, hmac⟩
    remaining := i.isLt
    rip := ripT.trans (by decide +kernel)
    indexRegister := ?_
    copyRegister := (abi.1 .r12 (by simp)).trans copyB
  }⟩
  exact (abi.1 .r14 (by simp)).trans
    ((setup.agrees.read (n := 64) (r := 14)
      (by simp [tailEffect, Effect.components, Write.component, Operand.component])).trans
      ((registerFrame.read (n := 64) (r := 14) (by simp)).trans state.indexRegister))

theorem bulk_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {i : Fin inputs.size} {consumed : Nat} {direct : Bool}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : BulkInput initial s salt inputs i consumed direct) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      InputDone initial t salt inputs i.val false := by
  obtain ⟨first, u, runU, readyU, stateU⟩ := bulk_blocks ctx ready state
  obtain ⟨second, t, runT, readyT, stateT⟩ := bulk_tail ctx readyU stateU
  exact ⟨first + second, t, runU.trans runT, readyT, stateT⟩

end Hkdf.Proofs.Standard.Update
