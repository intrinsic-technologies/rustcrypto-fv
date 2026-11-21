import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Head
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Last
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Setup
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Zero

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem first [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message chunk : ByteArray} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message) (input : Working initial s boundary message hash)
    (rip : s.RIP = 0x10d77e)
    (bytes : (MemoryRegion.mk (frameBase initial + 128).toNat 64).HasBytes s.external chunk) :
    ∃ t, Working initial t boundary message
      (SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits chunk)) ∧
      t.RIP = 0x10d7f5 := by
  obtain ⟨a, stateA, ripA, bytesA, highA, agreesA⟩ :=
    first_head_result pre input.toHashAt rip (by
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using bytes)
  obtain ⟨b, stateB, ripB, bytesB, agreesB⟩ :=
    copy_lower false pre stateA ripA bytesA highA
  have bytesB' : (MemoryRegion.mk (frameBase initial).toNat 64).HasBytes
      b.external chunk := by
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using bytesB
  obtain ⟨t, stateT, ripT, saved⟩ := setup_call false pre stateB ripB bytesB'
  refine ⟨t, ⟨stateT, ?_, ?_⟩, ripT⟩
  · exact (saved .r12 (by simp)).trans
      ((agreesB.read (n := 64) (r := 12) (by simp)).trans
        ((agreesA.read (n := 64) (r := 12) (by simp)).trans input.blocks))
  · exact (saved .r15 (by simp)).trans
      ((agreesB.read (n := 64) (r := 15) (by simp)).trans
        ((agreesA.read (n := 64) (r := 15) (by simp)).trans input.tailLength))

theorem last [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message)
    (input : LengthReady initial s boundary message hash) :
    ∃ t, HashAt initial t boundary
      (SHA256.Reference.compress hash
        (Standards.NIST.SHA2.bytesToBits (SHA256.finalBlock message))) ∧
      t.RIP = 0x10d8ce := by
  obtain ⟨a, stateA, ripA, bytesA, highA⟩ := last_head_result pre input
  obtain ⟨b, stateB, ripB, bytesB, _⟩ := copy_lower true pre stateA ripA bytesA highA
  have bytesB' : (MemoryRegion.mk (frameBase initial).toNat 64).HasBytes
      b.external (SHA256.finalBlock message) := by
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using bytesB
  obtain ⟨t, stateT, ripT, _⟩ := setup_call true pre stateB ripB bytesB'
  exact ⟨t, stateT, ripT⟩

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
