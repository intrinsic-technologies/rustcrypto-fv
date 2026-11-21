import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Preserve
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.BranchMachine
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.LengthMachine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem branch [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (input : Padded initial s boundary message) :
    ∃ t, Working initial t boundary message (SHA256.compressBlocks SHA256.initialHash message) ∧
      t.RIP = (if message.size % 64 < 56 then 0x10d849 else 0x10d77e) ∧
      (MemoryRegion.mk (frameBase initial + 128).toNat 64).HasBytes t.external (SHA256.paddedBuffer message) := by
  obtain ⟨t, run, ready, rip, frame⟩ := BranchMachine.branch
    (readyToStep input.machine input.bindingsSupported) input.loaded input.rip pre.outerBoundary
  have memory := frame.external (by simp [Component.Covers])
  have live := live_after_registers input.toLive run ready frame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨⟨live, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [SHA256.HashStateAt, memory] using input.hash
  · exact (frame.read (n := 64) (r := 3) (by simp)).trans input.hashPointer
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans input.count
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.position
  · rw [rip, input.remaining, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 63 - message.size % 64 < 2^64)]
    split <;> split <;> first | rfl | omega
  · simpa only [memory] using input.buffer

theorem length [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {hash : Array UInt32} (pre : Message.Pre initial boundary message)
    (input : Working initial s boundary message hash) (rip : s.RIP = 0x10d849)
    (prefixBytes : (MemoryRegion.mk (frameBase initial + 128).toNat 56).HasBytes
      s.external (SHA256.finalPrefix message)) :
    ∃ t, LengthReady initial t boundary message hash := by
  obtain ⟨_, t, run, ready, _, effect⟩ := LengthMachine.run boundary pre.outerBoundary
    s (readyToStep input.machine input.bindingsSupported) (LengthMachine.code input.loaded) rip
  have frame : AgreesExcept [.reg 12,.reg 15,.flags,.rip] s t := effect.agrees
  have memory := frame.external (by simp [Component.Covers])
  have live := live_after_registers input.toLive run ready frame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨⟨live, ?_, ?_⟩, effect.rip, ?_, ?_⟩⟩
  · simpa only [SHA256.HashStateAt, memory] using input.hashWords
  · exact (frame.read (n := 64) (r := 3) (by simp)).trans input.hashPointer
  · simpa only [memory] using prefixBytes
  · have output := effect.writes.2
    change t.regValue .r15 = Common.Instructions.bswap64
      (((s.regValue .r15).setWidth 32 <<< 3).setWidth 64 ||| (s.regValue .r12 <<< 9)) at output
    rw [output, input.tailLength, input.blocks]
    congr 1
    exact SHA256.length_word message.size

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress
