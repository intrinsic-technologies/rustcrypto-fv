import Sha2.Proofs.Common.SHA256.Absorb.Proof.Small.Transport
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem tail [Bindings] {l : Layout} {initial before s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (rip : s.RIP = l.pc .tailStore) (large : 64 - prior.size % 64 ≤ input.bytes.size)
    (count : Blocks.readReg s l.registers.remaining = BitVec.ofNat 64 ((prior ++ input.bytes).size % 64))
    (words : HashStateAt s (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes)))
    (blocks : memLoad s.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes).size / 64))
    (bytes : (⟨(Blocks.readReg s l.alignedSource).toNat, (prior ++ input.bytes).size % 64⟩ : MemoryRegion).HasBytes s.external (remainderBytes (prior ++ input.bytes)))
    (bounded : (⟨(Blocks.readReg s l.alignedSource).toNat,
      (prior ++ input.bytes).size % 64⟩ : MemoryRegion).Bounded)
    (apart : (⟨(Blocks.readReg s l.alignedSource).toNat,
      (prior ++ input.bytes).size % 64⟩ : MemoryRegion).Disjoint (Stack.region initial reserve))
    (bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial))
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer (l.sp initial))
    (targetRegister : ∀ r, l.tailCall.encoding = .register r → Blocks.readReg s r = 0x10dd60) :
    ∃ t, Finished l initial before t regions prior input := by
  let len := (prior ++ input.bytes).size % 64
  have small : len < 64 := Nat.mod_lt _ (by decide)
  have localState := Preserved.initial state.state state.rsp
  obtain ⟨u, stateU, store⟩ := run_stage ctx localState .tailStore rfl rip bufferRegister
    (by intro h; cases h)
  have readU (r : BitVec 4) : Blocks.readReg u r = Blocks.readReg s r :=
    store.agrees.read (by simp [Stage.effect, Effect.components, Write.component, Operand.component])
  have bufferU : ∀ r ∈ l.bufferSource, Blocks.readReg u r = l.buffer (l.sp initial) :=
    fun r member => (readU r).trans (bufferRegister r member)
  have restoredU : ∀ r ∈ l.bufferRestore, Blocks.readReg u r = l.buffer (l.sp initial) :=
    fun r member => (readU r).trans (restored r member)
  have stored : u.external[l.buffer (l.sp initial) + 63]? = some (UInt8.ofNat len) := by
    have readable : MemReadable u (l.buffer (l.sp initial) + 63) 1 := by
      simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        stack_frame_readable ctx.stack (frame := l.frameBytes) (offset := l.bufferOffset + 63)
          (by have := ctx.wf.capacity; omega) stateU.state.allocated (by have := ctx.wf.bufferFits; omega)
    have value : memLoad u.external (l.buffer (l.sp initial) + 63) 8 =
        (BitVec.ofNat 64 len).setWidth 8 := by
      have h := store.writes
      change memLoad u.external (l.buffer (l.sp initial) + 63) 8 =
        (Blocks.readReg s l.registers.remaining).setWidth 8 at h
      exact h.trans (congrArg (fun x : BitVec 64 => x.setWidth 8) count)
    have byte := byte_of_memLoad8 readable value
    simpa only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2^64), Nat.mod_eq_of_lt (by omega : len < 2^8)] using byte
  obtain ⟨v, stateV, setup⟩ := run_stage ctx stateU .tailSetup rfl store.rip bufferU
    (fun _ => restoredU)
  have memoryV := setup.agrees.external
    (by simp [Stage.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have outputV : v.regValue .rdi = l.buffer (l.sp initial) + BitVec.ofNat 64 0 := by
    rw [BitVec.add_zero]
    exact setup.writes.1
  have sourceV : v.regValue .rsi = Blocks.readReg s l.alignedSource :=
    setup.writes.2.1.trans (readU _)
  have countV : v.regValue .rdx = BitVec.ofNat 64 len :=
    setup.writes.2.2.trans ((readU _).trans count)
  have sourceRegion : registerRegion v .rsi len =
      (⟨(Blocks.readReg s l.alignedSource).toNat, len⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceV]
  have bytesV : (registerRegion v .rsi len).HasBytes v.external
      (remainderBytes (prior ++ input.bytes)) := by
    rw [sourceRegion]
    apply Common.Memory.hasBytes_of_frame bytes bounded stateV.frame.memory
    intro region member a ha hb
    exact apart a ha (ctx.footprint_subset region member a hb)
  have targetsV : ∀ r, l.tailCall.encoding = .register r → Blocks.readReg v r = 0x10dd60 := by
    intro r encoding
    have kept := ctx.targets.copies l.tailCall (by simp)
    rw [encoding] at kept
    exact (stateV.frame.registers (r.setWidth 5)
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt) kept.2).trans
      (targetRegister r encoding)
  obtain ⟨t, stateT, post, copied, frame⟩ := copy ctx stateV l.tailCall (by simp) setup.rip
    outputV countV (by omega) bytesV (sourceRegion ▸ bounded) (sourceRegion ▸ apart) targetsV
    (by rw [ctx.flow.tailReturn]; exact ctx.code.exits.2)
  have frame' : MemoryWriteFrame v t
      #v[⟨(l.buffer (l.sp initial)).toNat, len⟩, ⟨(l.sp initial - 344).toNat, 344⟩] := by
    simpa only [registerRegion, outputV, BitVec.add_zero] using frame
  have kept (i : Nat) (bound : i < 104) (outside : len ≤ i) (different : i ≠ 63) :
      t.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
        s.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
    have copiedKept := ctx.buffer_frame_byte (writeOffset := 0) (count := len)
      (by simpa only [BitVec.add_zero] using frame') (by omega) bound (.inr (by omega))
    have storeKept := stage_buffer_byte .tailStore store bound (fun _ => different) (by simp)
    exact copiedKept.trans (by simpa only [memoryV] using storeKept)
  have wordsT : HashStateAt t (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes)) := by
    apply Wrapper.hashState_of_bytes words
    intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      kept (64+i) (by omega) (by omega) (by omega)
  have blocksT : memLoad t.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes).size / 64) := by
    rw [← blocks]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    simpa only [PhysicalMemory.read, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      kept (96+i) (by omega) (by omega) (by omega)
  have tailT : t.external[l.buffer (l.sp initial) + 63]? = some (UInt8.ofNat len) := by
    have same := ctx.buffer_frame_byte (writeOffset := 0) (count := len)
      (by simpa only [BitVec.add_zero] using frame') (by omega) (by decide : 63 < 104)
      (.inr (by omega))
    change t.external[l.buffer (l.sp initial) + 63]? = v.external[l.buffer (l.sp initial) + 63]? at same
    exact same.trans (by rw [memoryV]; exact stored)
  have restoredT : ∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer (l.sp initial) := by
    intro r member
    have h := ctx.flow.restoredSaved r member
    have registerV : Blocks.readReg v r = l.buffer (l.sp initial) :=
      (setup.agrees.read (h.2 .tailSetup (by simp) (l.sp initial) u)).trans (restoredU r member)
    obtain ⟨_, _, called, effect, result, _⟩ := post
    exact (call_result_register effect result
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (nonvolatile_extended h.1)).trans registerV
  refine ⟨t, ⟨⟨stateT.state, stateT.rsp, state.frame.trans stateT.frame⟩,
    ?_, ⟨wordsT, ?_, tailT, blocksT⟩, fun _ => restoredT⟩⟩
  · simpa only [ite_eq_right (by omega : ¬ input.bytes.size < 64 - prior.size % 64)] using
      post.1.trans ctx.flow.tailReturn
  · simpa only [registerRegion, outputV, BitVec.add_zero] using copied

end Sha2.Proofs.Common.SHA256.Absorb
