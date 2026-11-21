import Sha2.Proofs.Common.SHA256.Absorb.Proof.CompressionInput
import Sha2.Proofs.Common.SHA256.Absorb.Proof.FillRegisters
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem fill [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (data : Prepared l (l.sp initial) prior input {s with RIP := l.entry})
    (rip : s.RIP = l.pc .fillSetup) (large : 64 - prior.size % 64 ≤ input.bytes.size)
    (count : s.regValue .rdx = BitVec.ofNat 64 (64 - prior.size % 64))
    (remaining : Blocks.readReg s l.registers.remaining =
      BitVec.ofNat 64 (input.bytes.size - (64 - prior.size % 64)))
    (apart : input.region.Disjoint (Stack.region initial reserve)) :
    ∃ t, Preserved l initial before t regions ∧
      Aligned l (l.sp initial) prior input (64 - prior.size % 64) t ∧
      t.RIP = l.pc .count ∧
      (∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer (l.sp initial)) := by
  let gap := 64 - prior.size % 64
  have gapBound : gap ≤ input.bytes.size := large
  have fillSize := Wrapper.Absorb.filledBlock_size prior input.bytes large
  have prefixSize : (input.bytes.extract 0 gap).size = gap := by
    simp only [ByteArray.size_extract, Nat.min_eq_left gapBound, Nat.sub_zero]
  have localState := Preserved.initial state.state state.rsp
  obtain ⟨a, stateA, setup⟩ := run_stage ctx localState .fillSetup rfl rip data.bufferRegister
    (by intro h; cases h)
  have memoryA := setup.agrees.external
    (by simp [Stage.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have savedA : Blocks.readReg a l.savedSource = input.address + BitVec.ofNat 64 gap := by
    have h := setup.writes.1
    change Blocks.readReg a l.savedSource = Blocks.readReg s l.registers.source + s.regValue .rdx at h
    have source : Blocks.readReg s l.registers.source = input.address := data.source
    rw [h, source, count]
  have outputA : a.regValue .rdi = l.buffer (l.sp initial) + BitVec.ofNat 64 (prior.size % 64) :=
    setup.writes.2.1.trans (congrArg (l.buffer (l.sp initial) + ·) data.position)
  have sourceA : a.regValue .rsi = input.address := setup.writes.2.2.trans data.source
  have countA : a.regValue .rdx = BitVec.ofNat 64 gap := by
    apply Eq.trans (setup.agrees.read (n := 64) (r := 2) ?_) count
    have h := nonvolatile_extended (ctx.flow.nonvolatile l.savedSource (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simpa [Stage.effect, Effect.components, Write.component, Operand.component] using Ne.symm h.2.2.1
  have remainingA : Blocks.readReg a l.registers.remaining = BitVec.ofNat 64 (input.bytes.size - gap) :=
    (fillSetup_register setup (ctx.flow.nonvolatile _ (by simp))
      (Ne.symm ctx.flow.fillRegisters.1)).trans remaining
  have bytesA : input.region.HasBytes a.external input.bytes := by rw [memoryA]; exact data.bytes
  obtain ⟨prefixBytes, prefixBounded, prefixApart⟩ := Common.Memory.input_slice bytesA data.bounded apart
    (offset := 0) (count := gap) (by omega)
  have sourceRegion : registerRegion a .rsi gap =
      (⟨(input.address + BitVec.ofNat 64 0).toNat, gap⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceA, BitVec.add_zero]
  obtain ⟨b, stateB, copyPost, copied, copyFrame⟩ := copy ctx stateA l.fillCall (by simp)
    setup.rip outputA countA (by dsimp [gap]; omega)
    (sourceRegion ▸ prefixBytes) (sourceRegion ▸ prefixBounded) (sourceRegion ▸ prefixApart)
    (stateA.copy_register ctx.targets (by simp) (data.copyRegister l.fillCall (by simp)))
    (by rw [ctx.flow.fillReturn]; exact ctx.code.inside .increment)
  have copyPost' := copyPost
  obtain ⟨_, _, calledCopy, copyEffect, copyResult, _⟩ := copyPost'
  have readCopy (r : BitVec 4) (member : r ∈ [l.registers.remaining, l.savedSource]) :
      Blocks.readReg b r = Blocks.readReg a r := by
    have nonvolatile := ctx.flow.nonvolatile r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl <;> simp)
    exact call_result_register copyEffect copyResult
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (nonvolatile_extended nonvolatile)
  have oldTail : (⟨(l.buffer (l.sp initial)).toNat, (remainderBytes prior).size⟩ : MemoryRegion).HasBytes a.external (remainderBytes prior) := by
    rw [memoryA]
    simpa only [remainderBytes_size] using data.hasher.tailBytes
  have filledB : (⟨(l.buffer (l.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes b.external
      (Wrapper.Absorb.filledBlock prior input.bytes) := by
    have joined := ctx.append_buffer_copy (front := remainderBytes prior) (back := input.bytes.extract 0 gap)
      (by rw [remainderBytes_size, prefixSize]; dsimp [gap]; omega) oldTail
      (by simpa only [registerRegion, outputA, remainderBytes_size, Nat.zero_add, prefixSize] using copied)
      (by simpa only [registerRegion, outputA, remainderBytes_size, prefixSize] using copyFrame)
    change (⟨(l.buffer (l.sp initial)).toNat, (Wrapper.Absorb.filledBlock prior input.bytes).size⟩ : MemoryRegion).HasBytes
      b.external (Wrapper.Absorb.filledBlock prior input.bytes) at joined
    rw [fillSize] at joined
    exact joined
  have unchanged (i : Nat) (bound : i < 104) (outside : 64 ≤ i) :
      b.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
      s.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
    have h := ctx.buffer_frame_byte (by simpa only [registerRegion, outputA] using copyFrame)
      (by dsimp [gap]; omega) bound (.inr (by dsimp [gap]; omega))
    exact h.trans (by rw [memoryA])
  have wordsB : HashStateAt b (l.buffer (l.sp initial) + 64) (compressBlocks l.initialHash prior) := by
    apply Wrapper.hashState_of_bytes data.hasher.hashWords
    intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      unchanged (64+i) (by omega) (by omega)
  have blocksB : memLoad b.external (l.buffer (l.sp initial) + 96) 64 = BitVec.ofNat 64 (prior.size / 64) := by
    rw [← data.hasher.blocks]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, PhysicalMemory.read] using
      unchanged (96+i) (by omega) (by omega)
  obtain ⟨c, stateC, increment⟩ := run_stage ctx stateB .increment rfl
    (copyPost.1.trans ctx.flow.fillReturn) (stateB.buffer_register ctx.flow data.bufferRegister)
    (by intro h; cases h)
  have readIncrement (r : BitVec 4) : Blocks.readReg c r = Blocks.readReg b r :=
    increment.agrees.read (by simp [Stage.effect, Effect.components, Write.component, Operand.component])
  have blocksC : memLoad c.external (l.buffer (l.sp initial) + 96) 64 = BitVec.ofNat 64 (prior.size / 64 + 1) := by
    have h := increment.writes
    change memLoad c.external (l.buffer (l.sp initial) + 96) 64 =
      memLoad b.external (l.buffer (l.sp initial) + 96) 64 + 1 at h
    rw [h, blocksB, BitVec.ofNat_add]
    rfl
  have wordsC : HashStateAt c (l.buffer (l.sp initial) + 64) (compressBlocks l.initialHash prior) := by
    apply Wrapper.hashState_of_bytes wordsB
    intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      stage_buffer_byte .increment increment (by omega : 64+i<104) (by simp) (fun _ => by omega)
  have filledC : (⟨(l.buffer (l.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes c.external
      (Wrapper.Absorb.filledBlock prior input.bytes) := by
    refine ⟨filledB.1, ?_⟩
    intro i
    have bound : i.val < 64 := by have := i.isLt; omega
    have same := stage_buffer_byte .increment increment (by omega : i.val<104) (by simp) (fun _ => by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      same.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using filledB.2 i)
  obtain ⟨d, stateD, compressionSetup⟩ := run_stage ctx stateC .fillCompressSetup rfl increment.rip
    (stateC.buffer_register ctx.flow data.bufferRegister) (by intro h; cases h)
  have memoryD := compressionSetup.agrees.external (by
    cases hr : l.bufferRestore <;>
      simp [Stage.effect, hr, Effect.components, Write.component, Operand.component, Component.Covers])
  have callCount : d.regValue .rdx = 1 := compressionSetup.writes.1
  have callOutput : d.regValue .rdi = l.buffer (l.sp initial) + 64 := compressionSetup.writes.2.1
  have callSource : d.regValue .rsi = l.buffer (l.sp initial) := by
    have w := compressionSetup.writes
    cases hr : l.bufferRestore with
    | none => simp only [Stage.effect, hr, Option.toList_none, List.map_nil, List.append_nil] at w; exact w.2.2
    | some r => simp only [Stage.effect, hr, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append] at w; exact w.2.2.1
  have restoredD : ∀ r ∈ l.bufferRestore, Blocks.readReg d r = l.buffer (l.sp initial) := by
    intro r member
    cases hr : l.bufferRestore with
    | none => simp [hr] at member
    | some q =>
      have same : q = r := by simpa [hr] using member
      subst r
      have w := compressionSetup.writes
      simp only [Stage.effect, hr, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append] at w
      exact w.2.2.2
  have remainingD : Blocks.readReg d l.registers.remaining = BitVec.ofNat 64 (input.bytes.size - gap) :=
    (fillCompressSetup_register compressionSetup (ctx.flow.nonvolatile _ (by simp))
      (fun r member => Ne.symm (ctx.flow.restored_ne_remaining member))).trans
      ((readIncrement _).trans ((readCopy _ (by simp)).trans remainingA))
  have savedD : Blocks.readReg d l.savedSource = input.address + BitVec.ofNat 64 gap :=
    (fillCompressSetup_register compressionSetup (ctx.flow.nonvolatile _ (by simp))
      (fun r member => Ne.symm (ctx.flow.restoreIndependent r member))).trans
      ((readIncrement _).trans ((readCopy _ (by simp)).trans savedA))
  obtain ⟨disp, encoding, _⟩ := ctx.targets.compressions l.fillCompressCall (by simp)
  have returnPC : l.fillCompressCall.pc + 5 = l.pc .clearTail := by
    have h := ctx.flow.fillCompressReturn
    rw [encoding] at h
    exact h
  obtain ⟨e, stateE, post, wordsE, frameE⟩ := compress ctx stateD l.fillCompressCall (by simp)
    compressionSetup.rip callOutput (fun u ready effect => ctx.fill_pre stateD.state stateD.rsp
      callSource callOutput callCount (by simpa only [memoryD] using filledC)
      (by simpa only [HashStateAt, memoryD] using wordsC)
      (returnPC ▸ ctx.code.inside .clearTail) ready effect)
  have post' := post
  obtain ⟨_, _, called, callEffect, callResult⟩ := post'
  have readCall (r : BitVec 4) (member : r ∈ [l.registers.remaining, l.savedSource]) :
      Blocks.readReg e r = Blocks.readReg d r := by
    have nonvolatile := ctx.flow.nonvolatile r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl <;> simp)
    exact call_result_register callEffect callResult.toCalleeResult
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (nonvolatile_extended nonvolatile)
  have blocksE : memLoad e.external (l.buffer (l.sp initial) + 96) 64 = BitVec.ofNat 64 (prior.size / 64 + 1) := by
    rw [← blocksC]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    have same := ctx.buffer_frame_byte (writeOffset := 64) (count := 32)
      (by simpa only [BitVec.ofNat_eq_ofNat] using frameE) (by decide) (by omega : 96+i<104) (.inr (by omega))
    simpa only [memoryD, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, PhysicalMemory.read] using same
  obtain ⟨f, stateF, clear⟩ := run_stage ctx stateE .clearTail rfl (post.1.trans returnPC)
    (stateE.buffer_register ctx.flow data.bufferRegister) (by intro h; cases h)
  obtain ⟨t, stateT, restore⟩ := run_stage ctx stateF .restoreSource rfl clear.rip
    (stateF.buffer_register ctx.flow data.bufferRegister) (by intro h; cases h)
  have memoryT := restore.agrees.external
    (by simp [Stage.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have readClear (r : BitVec 4) : Blocks.readReg f r = Blocks.readReg e r :=
    clear.agrees.read (by simp [Stage.effect, Effect.components, Write.component, Operand.component])
  have sourceT : Blocks.readReg t l.alignedSource = input.address + BitVec.ofNat 64 gap :=
    restore.writes.trans ((readClear _).trans ((readCall _ (by simp)).trans savedD))
  have remainingT : Blocks.readReg t l.registers.remaining = BitVec.ofNat 64 (input.bytes.size - gap) := by
    apply Eq.trans (restore.agrees.read ?_)
      ((readClear _).trans ((readCall _ (by simp)).trans remainingD))
    have different : l.registers.remaining.setWidth 5 ≠ l.alignedSource.setWidth 5 := by
      intro eq
      have same := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] at same
      exact ((List.pairwise_cons.mp ctx.flow.splitRegisters).1 l.registers.remaining (by simp))
        (BitVec.eq_of_toNat_eq same.symm)
    simpa [Stage.effect, Effect.components, Write.component, Operand.component] using different
  have untouched (i : Nat) (bound : i < 104) (outside : 64 ≤ i) :
      t.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
        e.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
    rw [memoryT]
    exact stage_buffer_byte .clearTail clear bound (fun _ => by omega) (by simp)
  have wordsT : HashStateAt t (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 gap)) := by
    refine Wrapper.hashState_of_bytes (s := e) (a := l.buffer (l.sp initial) + 64) ?_ ?_
    · change HashStateAt e (l.buffer (l.sp initial) + 64)
        (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 (64 - prior.size % 64)))
      rw [Wrapper.Absorb.compressBlocks_filled_prefix _ _ _ large]
      simpa only [compressBlocks_single _ _ fillSize] using wordsE
    · intro i hi
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
        untouched (64+i) (by omega) (by omega)
  have blocksT : memLoad t.external (l.buffer (l.sp initial) + 96) 64 = BitVec.ofNat 64 (prior.size / 64 + 1) := by
    rw [← blocksE]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, PhysicalMemory.read] using
      untouched (96+i) (by omega) (by omega)
  have filledCounts := Wrapper.Absorb.filled_prefix_counts prior input.bytes large
  refine ⟨t, {stateT with frame := state.frame.trans stateT.frame},
    ⟨stateT.rsp, large, filledCounts.1, wordsT, ?_, sourceT, remainingT⟩, restore.rip, ?_⟩
  · rw [filledCounts.2]
    exact blocksT
  · exact restored_of_stage ctx.flow (by simp) restore
      (restored_of_stage ctx.flow (by simp) clear
        (restored_of_call ctx.flow callEffect callResult.toCalleeResult restoredD))

end Sha2.Proofs.Common.SHA256.Absorb
