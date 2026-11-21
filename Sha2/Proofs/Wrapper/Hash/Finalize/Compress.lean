import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Head
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Last
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Setup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256

theorem compress_first [Bindings] (body : Compression.BlockCorrect)
    {initial s : RamState} {inputs : Array Input} {message chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : Working initial s message hash v) (rip : s.RIP = (v.pc 0x206))
    (bytes : (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, Working initial t message (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk)) v
      ∧ t.RIP = (v.pc 0x276) := by
  obtain ⟨a, stateA, ripA, bytesA, highA, frameA⟩ :=
    Compress.first ctx input.toHashAt rip bytes
  obtain ⟨b, stateB, ripB, bytesB, frameB⟩ :=
    Compress.copy_lower false ctx stateA ripA bytesA highA
  obtain ⟨t, output, ripT, abi⟩ := Compress.setup_call body false ctx stateB ripB bytesB
  refine ⟨t, ⟨output, ?_, ?_⟩, ripT⟩
  · exact (abi.1 .r12 (by simp)).trans
      ((frameB.read (n := 64) (r := 12) (by simp)).trans
        ((frameA.read (n := 64) (r := 12) (by simp)).trans input.blocks))
  · exact (abi.1 .r15 (by simp)).trans
      ((frameB.read (n := 64) (r := 15) (by simp)).trans
        ((frameA.read (n := 64) (r := 15) (by simp)).trans input.tailLength))

theorem compress_last [Bindings] (body : Compression.BlockCorrect)
    {initial s : RamState} {inputs : Array Input} {message : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : LengthReady initial s message hash v) :
    ∃ t, HashAt initial t
      (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits (finalBlock message))) v
      ∧ t.RIP = (v.pc 0x332) := by
  obtain ⟨a, stateA, ripA, bytesA, highA⟩ := Compress.last ctx input
  obtain ⟨b, stateB, ripB, bytesB, _⟩ :=
    Compress.copy_lower true ctx stateA ripA bytesA highA
  obtain ⟨t, output, ripT, _⟩ := Compress.setup_call body true ctx stateB ripB bytesB
  exact ⟨t, output, ripT⟩

end Sha2.Proofs.Wrapper.Hash.Finalize
