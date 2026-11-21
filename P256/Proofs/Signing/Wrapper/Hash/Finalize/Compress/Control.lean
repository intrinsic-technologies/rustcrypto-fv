import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Preserve
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.BranchMachine
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.LengthMachine

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem branch [Bindings] {initial start s : RamState} {secret message : ByteArray} (pre : HashEntry initial start secret message)
    (input : Padded initial start s message) :
    ∃ t, Working initial start t message (SHA256.compressBlocks SHA256.initialHash message) ∧
      t.RIP = (if message.size % 64 < 56 then 0x10293d else 0x10289f) ∧
      (MemoryRegion.mk (frameBase initial + 64).toNat 64).HasBytes t.external (SHA256.paddedBuffer message) := by
  obtain ⟨t, run, ready, rip, frame⟩ := BranchMachine.branch
    (readyToStep input.machine input.bindingsSupported) input.loaded input.rip (outside pre.context)
  have memory := frame.external (by simp [Component.Covers])
  have live := live_after_registers pre input.toLive run ready frame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨⟨live, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [SHA256.HashStateAt, memory] using input.hash
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.hashPointer
  · exact (frame.read (n := 64) (r := 14) (by simp)).trans input.count
  · exact (frame.read (n := 64) (r := 3) (by simp)).trans input.position
  · rw [rip, input.remaining, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 63 - message.size % 64 < 2^64)]
    split <;> split <;> first | rfl | omega
  · simpa only [memory] using input.buffer

theorem length [Bindings] {initial start s : RamState} {secret message : ByteArray} {hash : Array UInt32} (pre : HashEntry initial start secret message)
    (input : Working initial start s message hash) (rip : s.RIP = 0x10293d)
    (prefixBytes : (MemoryRegion.mk (frameBase initial + 64).toNat 56).HasBytes
      s.external (SHA256.finalPrefix message)) :
    ∃ t, LengthReady initial start t message hash := by
  obtain ⟨_, t, run, ready, _, effect⟩ := LengthMachine.run (returnBoundary initial) (outside pre.context)
    s (readyToStep input.machine input.bindingsSupported) (LengthMachine.code input.loaded) rip
  have frame : AgreesExcept [.reg 14,.reg 3,.flags,.rip] s t := effect.agrees
  have memory := frame.external (by simp [Component.Covers])
  have live := live_after_registers pre input.toLive run ready frame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨⟨live, ?_, ?_⟩, effect.rip, ?_, ?_⟩⟩
  · simpa only [SHA256.HashStateAt, memory] using input.hashWords
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.hashPointer
  · simpa only [memory] using prefixBytes
  · have output := effect.writes.2
    change t.regValue .rbx = Common.Instructions.bswap64
      (((s.regValue .rbx).setWidth 32 <<< 3).setWidth 64 ||| (s.regValue .r14 <<< 9)) at output
    rw [output, input.tailLength, input.blocks]
    congr 1
    exact SHA256.length_word message.size

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress
