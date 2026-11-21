import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Interface
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.LoadSetup
import P256.Proofs.SHA256.LengthEncoding
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem load [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Copied initial start s message) :
    ∃ t, Loaded initial start t message := by
  have setup : LoadSetup.Pre s := ⟨state.rip,
    stack_readable pre.context state.toFrame (by decide),
    stack_readable pre.context state.toFrame (by decide)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := LoadSetup.run (returnBoundary initial) (outside pre.context) s
    (readyToStep state.machine state.bindingsSupported) (LoadSetup.code state.loaded) setup
  have noMem : ∀ c ∈ (LoadSetup.effect s).components, ∀ a, ¬ c.Covers a := by
    simp [LoadSetup.effect, Effect.components, Component.Covers]
  have memory := effect.agrees.external noMem
  have frame := state.toFrame.after_registers pre.context run ready effect.agrees noMem
    (by simp [LoadSetup.effect, Effect.components])
    (by simp [LoadSetup.effect, Effect.components])
  have rsp : rspOf s = frameBase initial := state.rsp
  have position : (memLoad s.external (rspOf s + 127) 8).setWidth 64 =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [rsp, memLoad_8]
    change ((s.external[frameBase initial + 127]?).getD 0).toBitVec.setWidth 64 = _
    have hp := state.hash.position
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hp
    change s.external[frameBase initial + 127]? = some (UInt8.ofNat (message.size % 64)) at hp
    rw [hp]
    simp only [Option.getD_some, UInt8.toBitVec_ofNat']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have count : memLoad s.external (rspOf s + 160) 64 =
      BitVec.ofNat 64 (message.size / 64) := by
    have bytes := Bytes.of_memLoad (n := 64)
      (stack_readable pre.context state.toFrame (offset := 160) (len := 8) (by decide)).mem
    have h := state.hash.count
    rw [← rsp] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h
    exact Except.ok.inj (bytes.loadBytes64.symm.trans h)
  have fields := effect.writes
  change t.regValue .r15 = rspOf s + 128 ∧
    t.regValue .rbx = (memLoad s.external (rspOf s + 127) 8).setWidth 64 ∧
    t.regValue .r14 = memLoad s.external (rspOf s + 160) 64 ∧
    t.regValue .r12 = (memLoad s.external (rspOf s + 127) 8).setWidth 64 ^^^ 63 at fields
  refine ⟨t, {
    toLive := ⟨frame⟩
    rip := effect.rip
    hash := by simpa only [SHA256.HashStateAt, memory, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.hash.hash
    tail := by simpa only [MemoryRegion.HasBytes, memory] using state.hash.buffer
    hashPointer := fields.1.trans (congrArg (· + 128) rsp)
    count := fields.2.2.1.trans count
    position := fields.2.1.trans position
    remaining := ?_ }⟩
  · rw [fields.2.2.2, position]
    exact SHA256.tail_zero_count _ (Nat.mod_lt _ (by decide))

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad
