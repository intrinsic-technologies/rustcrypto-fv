import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Interface
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.LoadSetup
import P256.Proofs.SHA256.LengthEncoding
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem load [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Copied initial s boundary message) :
    ∃ t, Loaded initial t boundary message := by
  have setup : LoadSetup.Pre s := ⟨state.rip,
    ScalarFrame.stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide),
    ScalarFrame.stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := LoadSetup.run boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported) (LoadSetup.code state.loaded) setup
  have noMem : ∀ c ∈ (LoadSetup.effect s).components, ∀ a, ¬ c.Covers a := by
    simp [LoadSetup.effect, Effect.components, Component.Covers]
  have memory := effect.agrees.external noMem
  have frame := state.toFrameState.after_registers ready effect.agrees noMem
    (by simp [LoadSetup.effect, Effect.components])
    (by simp [LoadSetup.effect, Effect.components])
    (by simp [LoadSetup.effect, Effect.components])
    (by simp [LoadSetup.effect, Effect.components])
  have rsp : rspOf s = frameBase initial := state.rsp
  have position : (memLoad s.external (rspOf s + 191) 8).setWidth 64 =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [rsp, memLoad_8]
    change ((s.external[frameBase initial + 191]?).getD 0).toBitVec.setWidth 64 = _
    have pos := state.hash.position
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at pos
    change s.external[frameBase initial + 191]? = some (UInt8.ofNat (message.size % 64)) at pos
    rw [pos]
    simp only [Option.getD_some, UInt8.toBitVec_ofNat']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have count : memLoad s.external (rspOf s + 224) 64 =
      BitVec.ofNat 64 (message.size / 64) := by
    have bytes := Bytes.of_memLoad (n := 64)
      (ScalarFrame.stack_readable pre.toCalleePre state.toFrameState
        (by decide) (offset := 224) (len := 8) (by decide)).mem
    have h := state.hash.count
    rw [← rsp] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact Except.ok.inj (bytes.loadBytes64.symm.trans h)
  have fields := effect.writes
  change t.regValue .rbx = rspOf s + 192 ∧
    t.regValue .r15 = (memLoad s.external (rspOf s + 191) 8).setWidth 64 ∧
    t.regValue .r12 = memLoad s.external (rspOf s + 224) 64 ∧
    t.regValue .r14 = (memLoad s.external (rspOf s + 191) 8).setWidth 64 ^^^ 63 at fields
  refine ⟨t, {
    toLive := {
      toFrameState := frame
      execution := ?_
      savedKey := by rw [memory]; exact state.savedKey
      savedOutput := by rw [memory]; exact state.savedOutput
      savedSignature := by rw [memory]; exact state.savedSignature
      stackFrame := ?_ }
    rip := effect.rip
    hash := by simpa only [SHA256.HashStateAt, memory, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.hash.hash
    tail := by simpa only [MemoryRegion.HasBytes, memory] using state.hash.buffer
    hashPointer := fields.1.trans (congrArg (· + 192) rsp)
    count := fields.2.2.1.trans count
    position := fields.2.1.trans position
    remaining := ?_ }⟩
  · obtain ⟨before, beforeRun⟩ := state.execution
    exact ⟨before + fuel, beforeRun.trans run⟩
  · intro a outside
    rw [memory]
    exact state.stackFrame a outside
  · rw [fields.2.2.2, position]
    exact SHA256.tail_zero_count _ (Nat.mod_lt _ (by decide))

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad
