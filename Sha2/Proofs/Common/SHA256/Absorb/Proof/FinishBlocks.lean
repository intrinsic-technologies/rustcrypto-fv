import Sha2.Proofs.Common.SHA256.Absorb.Proof.Aligned
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Tail
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Registers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem finish_blocks [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve consumed : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (rip : s.RIP = l.pc .splitTail) (large : 64 - prior.size % 64 ≤ input.bytes.size)
    (consumedBound : consumed ≤ input.bytes.size)
    (aligned : (prior ++ input.bytes.extract 0 consumed).size % 64 = 0)
    (messageBound : prior.size + input.bytes.size < 2^61)
    (source : Blocks.readReg s l.alignedSource = input.address + BitVec.ofNat 64 consumed)
    (length : Blocks.readReg s l.registers.remaining = BitVec.ofNat 64 (input.bytes.size - consumed))
    (words : HashStateAt s (l.buffer (l.sp initial) + 64)
      (compressBlocks (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 consumed))
        (input.bytes.extract consumed (consumed + 64 * ((input.bytes.size - consumed) / 64)))))
    (blocks : memLoad s.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes.extract 0 consumed).size / 64 +
        (input.bytes.size - consumed) / 64))
    (bytes : input.region.HasBytes s.external input.bytes) (bounded : input.region.Bounded)
    (apart : input.region.Disjoint (Stack.region initial reserve))
    (bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial))
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer (l.sp initial))
    (targetRegister : ∀ r, l.tailCall.encoding = .register r → Blocks.readReg s r = 0x10dd60) :
    ∃ t, Finished l initial before t regions prior input := by
  obtain ⟨u, stateU, split⟩ := run_stage ctx (Preserved.initial state.state state.rsp)
    .splitTail rfl rip bufferRegister (by intro h; cases h)
  have values := split_values length source (by omega) split
  have memory := split.agrees.external
    (by simp [Stage.effect, Blocks.effect, Effect.components, Write.component,
      Operand.component, Component.Covers])
  have counts := Wrapper.Absorb.Blocks.finish_counts prior input.bytes consumedBound aligned
  have finalWords : HashStateAt u (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash (prior ++ input.bytes)) := by
    apply Wrapper.hashState_of_bytes (s := s)
      (by simpa only [Wrapper.Absorb.Blocks.finish_hash _ _ _ consumedBound aligned] using words)
    intro i hi
    rw [memory]
  have finalBlocks : memLoad u.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 ((prior ++ input.bytes).size / 64) := by
    rw [memory, blocks, counts.1]
  have finalLength : Blocks.readReg u l.registers.remaining =
      BitVec.ofNat 64 ((prior ++ input.bytes).size % 64) := by
    rw [counts.2]
    exact values.1
  have bytesU : input.region.HasBytes u.external input.bytes := by rw [memory]; exact bytes
  obtain ⟨tailBytes, tailBounded, tailApart⟩ := Common.Memory.input_slice bytesU bounded apart
    (offset := consumed + 64 * ((input.bytes.size - consumed) / 64))
    (count := (input.bytes.size - consumed) % 64) (by omega)
  have endEq : consumed + 64 * ((input.bytes.size - consumed) / 64) +
      (input.bytes.size - consumed) % 64 = input.bytes.size := by omega
  have regionEq :
      (⟨(Blocks.readReg u l.alignedSource).toNat, (prior ++ input.bytes).size % 64⟩ : MemoryRegion) =
      ⟨(input.address + BitVec.ofNat 64 (consumed + 64 * ((input.bytes.size - consumed) / 64))).toNat,
        (input.bytes.size - consumed) % 64⟩ := by
    rw [values.2, counts.2, BitVec.add_assoc, ← BitVec.ofNat_add]
  have finalBytes :
      (⟨(Blocks.readReg u l.alignedSource).toNat, (prior ++ input.bytes).size % 64⟩ : MemoryRegion).HasBytes u.external (remainderBytes (prior ++ input.bytes)) := by
    rw [regionEq, Wrapper.Absorb.Blocks.finish_tail prior input.bytes consumedBound aligned]
    simpa only [endEq] using tailBytes
  obtain ⟨t, finished⟩ := tail ctx stateU split.rip large finalLength finalWords finalBlocks
    finalBytes (regionEq ▸ tailBounded) (regionEq ▸ tailApart)
    (stateU.buffer_register ctx.flow bufferRegister)
    (restored_of_stage ctx.flow (by simp) split restored)
    (stateU.copy_register ctx.targets (by simp) targetRegister)
  exact ⟨t, {finished with frame := state.frame.trans finished.frame}⟩

end Sha2.Proofs.Common.SHA256.Absorb
