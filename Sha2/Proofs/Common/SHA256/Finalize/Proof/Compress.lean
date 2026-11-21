import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Copy
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Last
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Setup
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Call

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compress_first [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    {message chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve)
    (input : Working L initial before s regions message hash) (rip : s.RIP = L.firstHead)
    (bytes : (⟨(L.buffer (L.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, Working L initial before t regions message
      (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk)) ∧ t.RIP = L.zero := by
  obtain ⟨a,stateA,ripA,bytesA,highA,frameA⟩ := Compress.first ctx input.toHashAt rip bytes
  obtain ⟨b,stateB,ripB,bytesB,frameB⟩ := Compress.lower false ctx stateA ripA bytesA highA
  obtain ⟨u,stateU,ripU,rdi,rsi,count,memory,tail,blocks,_⟩ := Compress.setup false ctx stateB ripB
  obtain ⟨t,output,ripT,abi⟩ := Compress.call false ctx stateU ripU rdi rsi count
    (by simpa only [memory] using bytesB)
  refine ⟨t,⟨output,?_,?_⟩,ripT⟩
  · exact (Compress.abi_read abi (by cases L.variant <;> decide)).trans (tail.trans
      ((frameB.read (n := 64) (r := L.variant.registers.tail) (by
        cases L.variant <;> simp [Variant.registers,Blocks.Length.Registers.tail])).trans
        ((frameA.read (n := 64) (r := L.variant.registers.tail) (by
          cases L.variant <;> simp [Variant.registers,Blocks.Length.Registers.tail])).trans input.tailLength)))
  · exact (Compress.abi_read abi (by cases L.variant <;> decide)).trans (blocks.trans
      ((frameB.read (n := 64) (r := L.variant.registers.blocks) (by
        cases L.variant <;> simp [Variant.registers,Blocks.Length.Registers.blocks])).trans
        ((frameA.read (n := 64) (r := L.variant.registers.blocks) (by
          cases L.variant <;> simp [Variant.registers,Blocks.Length.Registers.blocks])).trans input.blocks)))

theorem compress_last [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    {message : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve)
    (input : LengthReady L initial before s regions message hash) :
    ∃ t, HashAt L initial before t regions
      (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits (finalBlock message))) ∧
      t.RIP = L.exit ∧ (.reg L.variant.hashReg : Operand 64).read t = L.hash (L.sp initial) := by
  obtain ⟨a,stateA,ripA,bytesA,highA⟩ := Compress.last ctx input
  obtain ⟨b,stateB,ripB,bytesB,_⟩ := Compress.lower true ctx stateA ripA bytesA highA
  obtain ⟨u,stateU,ripU,rdi,rsi,count,memory,_,_,pointer⟩ := Compress.setup true ctx stateB ripB
  obtain ⟨t,output,ripT,abi⟩ := Compress.call true ctx stateU ripU rdi rsi count
    (by simpa only [memory] using bytesB)
  exact ⟨t,output,ripT,(Compress.abi_read abi (by cases L.variant <;> decide)).trans (pointer rfl)⟩

end Sha2.Proofs.Common.SHA256.Finalize
