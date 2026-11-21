import Sha2.Proofs.Wrapper.Hash.Finalize.State
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper.Hash.LengthEncoding
import Sha2.Proofs.Wrapper.Hash.CopyHashBuffer
import Sha2.Proofs.Wrapper.Hash.Padding.LoadSetup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256

structure Loaded [Bindings] (initial s : RamState) (message : ByteArray) (v : Variant := .sha256)
    : Prop
    extends Working initial s message (compressBlocks v.initialHash message) v where
  rip : s.RIP = (v.pc 0x1e5)
  tailBytes : (⟨(stackPtr initial - 344).toNat, message.size % 64⟩ : MemoryRegion).HasBytes
    s.external (remainderBytes message)
  paddingLength : s.regValue .rbx = BitVec.ofNat 64 (63 - message.size % 64)

theorem load [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (input : Buffered initial s message v) (rip : s.RIP = (v.pc 0x1bb)) :
    ∃ t, Loaded initial t message v := by
  obtain ⟨u, stateU, ripU, rspU, copied, copyFrame⟩ :=
    copy_hash_buffer ctx input.toState rip input.rsp
  have localCopy : Wrapper.LocalWrites initial
      [.reg 1, .reg 6, .reg 7, .mem (stackPtr initial - 344) 104, .rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact Wrapper.local_memory (by decide) (by decide) (by decide) a ha
  have preservedU : Preserved initial u v :=
    Wrapper.preserved_of_bytes input.toPreserved stateU rspU
      (fun a ha => localCopy.memory copyFrame ha)
  have hashU : HashStateAt u (stackPtr initial - 280)
      (compressBlocks v.initialHash message) := by
    apply Wrapper.hashState_of_bytes input.hashWords
    intro i hi
    have byte := copied (64 + i) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
    simpa only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  have tailU : u.external[stackPtr initial - 281]? = some (UInt8.ofNat (message.size % 64)) := by
    have byte := copied 63 (by decide)
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at byte
    have byte' : u.external[stackPtr initial - 281]? = s.external[stackPtr initial - 89]? := by
      simpa only [BitVec.sub_eq_add_neg, BitVec.reduceNeg] using byte
    exact byte'.trans input.tailLength
  have blocksU : memLoad u.external (stackPtr initial - 248) 64 =
      BitVec.ofNat 64 (message.size / 64) := by
    apply Eq.trans _ input.blocks
    apply memLoad_congr
    intro i hi
    have byte := copied (96 + i) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
    have equal : u.external[stackPtr initial - 248 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 56 + BitVec.ofNat 64 i]? := by
      simpa only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
    change (u.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [equal]
  have pre : Padding.LoadSetup.Pre u v := by
    refine ⟨ripU, ?_, ?_⟩
    all_goals rw [stack_address rspU]
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_readable ctx stateU (by decide) (by decide)
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  obtain ⟨_, t, run, ready, _, effect⟩ := Padding.LoadSetup.run (v := v) (returnBoundary initial)
    outside u (supportedMachine_readyToStep stateU.machine) (Padding.LoadSetup.code (v := v) stateU.loaded) pre
  have noMem : ∀ c ∈ (Padding.LoadSetup.effect u v).components, ∀ a, ¬ c.Covers a := by
    simp [Padding.LoadSetup.effect, Effect.components, Component.Covers]
  have frame := effect.agrees
  have preservedT := Wrapper.preserved_of_agrees ctx preservedU run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by simp [Padding.LoadSetup.effect, Effect.components])
    (by simp [Padding.LoadSetup.effect, Effect.components])
  have memory := frame.external noMem
  have lengthRead : (memLoad u.external (rspOf u + 63) 8).setWidth 64 =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [stack_address rspU]
    change (memLoad u.external (stackPtr initial - 281) 8).setWidth 64 = _
    rw [memLoad_8]
    change ((u.external[stackPtr initial - 281]?).getD 0).toBitVec.setWidth 64 = _
    rw [tailU]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec, UInt8.toNat_ofNat']
    have := Nat.mod_lt message.size (by decide : 0 < 64)
    omega
  have writes := effect.writes
  change t.regValue .r14 = rspOf u + 64 ∧
    t.regValue .r15 = (memLoad u.external (rspOf u + 63) 8).setWidth 64 ∧
    t.regValue .r12 = memLoad u.external (rspOf u + 96) 64 ∧
    t.regValue .rbx = (memLoad u.external (rspOf u + 63) 8).setWidth 64 ^^^ 63 at writes
  refine ⟨t, ⟨⟨preservedT, ?_, ?_⟩, ?_, ?_⟩, effect.rip, ?_, ?_⟩
  · simpa only [HashStateAt, memory] using hashU
  · rw [writes.1, stack_address rspU]
    rfl
  · rw [writes.2.2.1, stack_address rspU]
    exact blocksU
  · exact writes.2.1.trans lengthRead
  · refine ⟨input.tailBytes.1, ?_⟩
    intro i
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 344).toNat + i.val)]? = _
    rw [memory, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hi : i.val < message.size % 64 := by
      simpa only [remainderBytes_size] using i.isLt
    rw [copied i.val (by omega)]
    have byte := input.tailBytes.2 i
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, remainderBytes] using byte
  · rw [writes.2.2.2, lengthRead]
    exact tail_zero_count _ (Nat.mod_lt _ (by decide))

end Sha2.Proofs.Wrapper.Hash.Finalize.Pad
