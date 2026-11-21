import Sha2.Proofs.Common.SHA256.Absorb.Proof.FinishBlocks
import Sha2.Proofs.Common.SHA256.Absorb.Proof.CompressionInput
import Sha2.Proofs.Common.SHA256.Absorb.Proof.BulkRegisters

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem bulk_tail [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve consumed : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (data : Aligned l (l.sp initial) prior input consumed s)
    (rip : s.RIP = if (input.bytes.size - consumed) / 64 = 0 then l.pc .splitTail else l.pc .addBlocks)
    (count : s.regValue .rdx = BitVec.ofNat 64 ((input.bytes.size - consumed) / 64))
    (large : 64 - prior.size % 64 ≤ input.bytes.size)
    (messageBound : prior.size + input.bytes.size < 2^61)
    (bytes : input.region.HasBytes s.external input.bytes) (bounded : input.region.Bounded)
    (apart : input.region.Disjoint (Stack.region initial reserve))
    (bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial))
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer (l.sp initial))
    (targetRegister : ∀ r, l.tailCall.encoding = .register r → Blocks.readReg s r = 0x10dd60) :
    ∃ t, Finished l initial before t regions prior input := by
  by_cases zero : (input.bytes.size - consumed) / 64 = 0
  · apply finish_blocks ctx state (by simpa only [zero, ite_true] using rip) large
      data.consumedBound data.aligned messageBound data.source data.length ?_ ?_
      bytes bounded apart bufferRegister restored targetRegister
    · simpa [zero, compressBlocks, compressBlocksFrom] using data.hashWords
    · simpa only [zero, Nat.add_zero] using data.blocks
  have localState := Preserved.initial state.state state.rsp
  obtain ⟨a, stateA, add⟩ := run_stage ctx localState .addBlocks rfl
    (by simpa only [zero, ite_false] using rip) bufferRegister (by intro h; cases h)
  have readA (r : BitVec 5) : (.reg r : Operand 64).read a = (.reg r : Operand 64).read s :=
    add.agrees.read (by simp [Stage.effect, Effect.components, Write.component, Operand.component])
  have wordsA : HashStateAt a (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 consumed)) := by
    apply Wrapper.hashState_of_bytes data.hashWords
    intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      stage_buffer_byte .addBlocks add (by omega : 64+i<104) (by simp) (fun _ => by omega)
  have blocksA : memLoad a.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes.extract 0 consumed).size / 64 +
        (input.bytes.size - consumed) / 64) := by
    have h := add.writes
    change memLoad a.external (l.buffer (l.sp initial) + 96) 64 =
      memLoad s.external (l.buffer (l.sp initial) + 96) 64 + s.regValue .rdx at h
    rw [h, data.blocks, count, BitVec.ofNat_add]
  obtain ⟨b, stateB, setup⟩ := run_stage ctx stateA .bulkSetup rfl add.rip
    (stateA.buffer_register ctx.flow bufferRegister) (by intro h; cases h)
  have outputB : b.regValue .rdi = l.buffer (l.sp initial) + 64 := setup.writes.1
  have sourceB : b.regValue .rsi = input.address + BitVec.ofNat 64 consumed := by
    have source : b.regValue .rsi = Blocks.readReg a l.alignedSource := by
      have w := setup.writes
      cases hs : l.bulkSave with
      | none => simp only [Stage.effect, hs, Option.toList_none, List.map_nil, List.append_nil] at w; exact w.2
      | some r => simp only [Stage.effect, hs, Option.toList_some, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append] at w; exact w.2.1
    exact source.trans ((readA _).trans data.source)
  have countB : b.regValue .rdx = BitVec.ofNat 64 ((input.bytes.size - consumed) / 64) := by
    apply Eq.trans (setup.agrees.read (n := 64) (r := 2) ?_) ((readA 2).trans count)
    cases hs : l.bulkSave with
    | none => simp [Stage.effect, hs, Effect.components, Write.component, Operand.component]
    | some r =>
      have h := nonvolatile_extended (ctx.flow.bulkSaved.2 r (by simp [hs])).1
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simpa [Stage.effect, hs, Effect.components, Write.component, Operand.component,
        BitVec.ofNat_eq_ofNat] using Ne.symm h.2.2.1
  have memoryB := setup.agrees.external (by
    cases hs : l.bulkSave <;>
      simp [Stage.effect, hs, Effect.components, Write.component, Operand.component, Component.Covers])
  have wordsB : HashStateAt b (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 consumed)) := by
    simpa only [HashStateAt, memoryB] using wordsA
  have bytesB := ctx.input_bytes bytes bounded apart stateB.frame
  obtain ⟨fullBytes, fullBounded, fullApart⟩ := Common.Memory.input_slice bytesB bounded apart
    (offset := consumed) (count := 64 * ((input.bytes.size - consumed) / 64))
    (by have := data.consumedBound; omega)
  have regionB : registerRegion b .rsi (64 * ((input.bytes.size - consumed) / 64)) =
      (⟨(input.address + BitVec.ofNat 64 consumed).toNat,
        64 * ((input.bytes.size - consumed) / 64)⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceB]
  obtain ⟨disp, encoding, _⟩ := ctx.targets.compressions l.bulkCall (by simp)
  have returnPC : l.bulkCall.pc + 5 = l.pc .bulkRestore := by
    have h := ctx.flow.bulkReturn
    rw [encoding] at h
    exact h
  obtain ⟨c, stateC, post, wordsC, frameC⟩ := compress ctx stateB l.bulkCall (by simp)
    setup.rip outputB (fun u ready effect => ctx.bulk_pre stateB.state stateB.rsp outputB countB
      (regionB ▸ fullBytes) (regionB ▸ fullBounded) (regionB ▸ fullApart) wordsB
      (returnPC ▸ ctx.code.inside .bulkRestore) ready effect)
  obtain ⟨d, stateD, restore⟩ := run_stage ctx stateC .bulkRestore rfl
    (post.1.trans returnPC) (stateC.buffer_register ctx.flow bufferRegister) (by intro h; cases h)
  have fullPost := post
  obtain ⟨_, _, called, effect, result⟩ := fullPost
  have registers := bulk_registers ctx.flow setup effect result.toCalleeResult restore
  have memoryD := restore.agrees.external (by
    cases hs : l.bulkSave <;>
      simp [Stage.effect, hs, Effect.components, Write.component, Operand.component, Component.Covers])
  have blocksC : memLoad c.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes.extract 0 consumed).size / 64 +
        (input.bytes.size - consumed) / 64) := by
    rw [← blocksA]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    have h := ctx.buffer_frame_byte (writeOffset := 64) (count := 32)
      (by simpa only [BitVec.ofNat_eq_ofNat] using frameC) (by decide)
      (by omega : 96+i<104) (.inr (by omega))
    simpa only [PhysicalMemory.read, BitVec.add_assoc, ← BitVec.ofNat_add,
      BitVec.ofNat_eq_ofNat, memoryB] using h
  have restoredA := restored_of_stage ctx.flow (by simp) add restored
  have restoredB := restored_of_stage ctx.flow (by simp) setup restoredA
  have restoredC := restored_of_call ctx.flow effect result.toCalleeResult restoredB
  have restoredD := restored_of_stage ctx.flow (by simp) restore restoredC
  obtain ⟨t, finished⟩ := finish_blocks ctx stateD restore.rip large data.consumedBound data.aligned
    messageBound (registers.1.trans ((readA _).trans data.source))
    (registers.2.trans ((readA _).trans data.length))
    (by simpa only [HashStateAt, memoryD] using wordsC)
    (by simpa only [memoryD] using blocksC)
    (ctx.input_bytes bytes bounded apart stateD.frame) bounded apart
    (stateD.buffer_register ctx.flow bufferRegister) restoredD
    (stateD.copy_register ctx.targets (by simp) targetRegister)
  exact ⟨t, {finished with frame := state.frame.trans finished.frame}⟩

end Sha2.Proofs.Common.SHA256.Absorb
