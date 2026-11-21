import P256.Proofs.Verifying.Message.Hash.Long.Tail.Interface
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Finish
import P256.Proofs.Verifying.Message.Hash.Long.Input
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Ready initial s boundary message) :
    ∃ t, Buffered initial t boundary message := by
  have destination : s.regValue .rdi = stackPtr initial - 704 := by
    rw [state.destination]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨u, copied⟩ := Copy.copy pre state.toFrameState state.stackFrame
    (sourceOffset := 64 * (message.size / 64)) (count := message.size % 64)
    (outputOffset := 704) (by omega) (by decide) (by omega)
    0xd6fa 0xf6df8 (by decide) (by decide +kernel) (by decide)
    state.rip state.source destination state.length
  have kept {offset len : Nat} (bound : offset ≤ 1176) (span : len ≤ offset + 8)
      (apart : 704 + len ≤ offset ∨ offset + message.size % 64 ≤ 704)
      {i : Nat} (hi : i < len) :=
    copied.stack_byte pre (by decide) bound span apart hi
  have sameWord {offset : Nat} (bound : offset ≤ 1176)
      (apart : 712 ≤ offset ∨ offset + message.size % 64 ≤ 704) :
      memLoad u.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun o : Option UInt8 => o.getD 0) (kept bound (by omega) apart hi)
  have hashU : HMAC.Sha256StateAt u (frameBase initial + 472) message := by
    constructor
    · have slice := (message_slice pre state.stackFrame
        (offset := 64 * (message.size / 64)) (count := message.size % 64) (by omega)).2.2
      have total : 64 * (message.size / 64) + message.size % 64 = message.size := by omega
      rw [total] at slice
      change (MemoryRegion.mk (memLoad initial.external (initial.regValue .rdx) 64 +
        BitVec.ofNat 64 (64 * (message.size / 64))).toNat (message.size % 64)).HasBytes
        s.external (SHA256.remainderBytes message) at slice
      have result := hasBytes_copy slice copied.copied
      have address : frameBase initial + 472 = stackPtr initial - 704 := by
        simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address]
      exact result
    · have h := kept (offset := 641) (len := 1) (by decide) (by decide) (.inr (by omega))
        (i := 0) (by decide)
      simp only [BitVec.add_zero] at h
      change u.external[stackPtr initial - 641]? = s.external[stackPtr initial - 641]? at h
      have pos : u.external[frameBase initial + 535]? = some (UInt8.ofNat (message.size % 64)) := by
        have addr : frameBase initial + 535 = stackPtr initial - 641 := by
          simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          rfl
        rw [← addr] at h
        exact h.trans state.position
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact pos
    · have hash : SHA256.HashStateAt s (stackPtr initial - 640)
          (SHA256.compressBlocks SHA256.initialHash message) := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hash
      have out := hash.copy (fun i hi => kept (offset := 640) (len := 32)
        (by decide) (by decide) (.inr (by omega)) hi)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using out
    · have count : loadBytes s.external (stackPtr initial - 608) 8 =
          .ok (BitVec.ofNat 64 (message.size / 64)) := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.count
      have out := loadBytes_ok_copy (fun i hi => kept (offset := 608) (len := 8)
        (by decide) (by decide) (.inr (by omega)) hi) count
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using out
  have last : (Operand.reg 13 : Operand 64).read u + 16 = (Operand.reg 12 : Operand 64).read u := by
    change u.regValue .r13 + 16 = u.regValue .r12
    rw [copied.calleeSaved .r13 (by simp), copied.calleeSaved .r12 (by simp),
      state.current, state.endPointer]
  obtain ⟨t, runT, readyT, ripT, _, agreesT⟩ := Finish.run
    (readyToStep copied.machine copied.bindingsSupported) copied.loaded copied.rip last pre.outerBoundary
  have memoryT := agreesT.external (by simp [Component.Covers])
  have frameT := copied.toFrameState.after_registers readyT agreesT
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, frameT, ?_, ripT, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨before, runBefore⟩ := state.execution
    obtain ⟨fuel, runCopy⟩ := copied.execution
    exact ⟨before + fuel + 4, (runBefore.trans runCopy).trans runT⟩
  · exact hashU.copy (fun _ _ => by rw [memoryT])
  · rw [memoryT]
    have h := sameWord (offset := 720) (by decide) (.inl (by decide))
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedKey)
  · rw [memoryT]
    have h := sameWord (offset := 792) (by decide) (.inl (by decide))
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedOutput)
  · rw [memoryT]
    have h := sameWord (offset := 712) (by decide) (.inl (by decide))
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedSignature)
  · intro address outside
    rw [memoryT]
    exact memoryWriteFrame_trans state.stackFrame
      (work_frame_stack pre.toCalleePre copied.writes) address outside

end P256.Proofs.Verifying.Message.Hash.Long.Tail
