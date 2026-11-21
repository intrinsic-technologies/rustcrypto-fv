import Hkdf.Proofs.Common.StreamPadding.Execution.Transport
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256

attribute [local simp] Variant.lengthReg Variant.lengthIndex Variant.blocksReg
  Variant.blocksIndex Variant.hashReg Variant.hashIndex Variant.remainingReg
  Variant.remainingIndex Variant.stableReg Variant.stableIndex regIndex X86.Syntax.Reg.fin


theorem first [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} {message : ByteArray} {hash : Array UInt32} (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .firstHead)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size%64))
    (blocks : s.regValue v.blocksReg = BitVec.ofNat 64 (message.size/64))
    (pointer : s.regValue v.hashReg = stackPtr s + BitVec.ofNat 64 v.hash)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 v.hash) hash)
    (bytes : (⟨(stackPtr s + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes
      s.external (tailFirst message)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧
      stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue v.stableReg = s.regValue v.stableReg ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control ∧ MemoryWriteFrame s t (writes v (stackPtr s)) ∧
      t.RIP = v.pc .length ∧
      t.regValue v.lengthReg = BitVec.ofNat 64 (message.size%64) ∧
      t.regValue v.blocksReg = BitVec.ofNat 64 (message.size/64) ∧
      t.regValue v.hashReg = stackPtr t + BitVec.ofNat 64 v.hash ∧
      HashStateAt t (stackPtr t + BitVec.ofNat 64 v.hash)
        (Hkdf.Proofs.NIST.SHA256.compress hash
          (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst message))) ∧
      (⟨(stackPtr t + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
        t.external ⟨Array.replicate 56 0⟩ := by
  obtain ⟨n,c,runC,readyC,runningC,effectC⟩ := copy v false pre running rsp rip
  obtain ⟨rspC,rbxC,stableC,mxcsrC,fcwC,frameC⟩ :=
    copy_summary v false effectC (local_bounds v pre rsp).2
  have readableC := local_readable v pre runningC (rspC.trans rsp) v.scratch 64
    (by cases v <;> decide)
  rw [rspC] at readableC
  have bytesC := copy_bytes v false effectC bytes readableC (by cases v <;> simp [] <;> decide)
  change (⟨(stackPtr s + BitVec.ofNat 64 v.scratch).toNat,64⟩ : MemoryRegion).HasBytes
    c.external (tailFirst message) at bytesC
  have hashC := copy_hash v false effectC words
  have args := effectC.writes
  change _ ∧ _ ∧ c.regValue .rsi = stackPtr s + BitVec.ofNat 64 v.scratch ∧
    c.regValue .rdx = 1 ∧ c.regValue .rdi = s.regValue v.hashReg ∧ _ at args
  obtain ⟨m,a,runA,readyA,runningA,ripA,rspA,abiA,frameA,_,hashA⟩ :=
    compress v false pre runningC (rspC.trans rsp) effectC.rip
      (by simpa only [rspC] using args.2.2.2.2.1.trans pointer)
      (by simpa only [rspC] using args.2.2.1) args.2.2.2.1
      (by rw [rspC]; exact bytesC) (by simpa only [rspC] using hashC)
  obtain ⟨k,t,runT,readyT,runningT,effectT⟩ := zero v pre runningA
    ((rspA.trans rspC).trans rsp) ripA
  obtain ⟨rspT,rbxT,stableT,mxcsrT,fcwT⟩ := stable_of_agrees_selected v effectT.agrees
    (by cases v <;> simp [Stages.zeroEffect, Effect.components, Write.component, Operand.component] <;> decide)
  have hashT : HashStateAt t (stackPtr a + BitVec.ofNat 64 v.hash)
      (Hkdf.Proofs.NIST.SHA256.compress hash
        (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst message))) := by
    apply Hkdf.Proofs.Common.hashState_of_bytes
      (show HashStateAt a (stackPtr a + BitVec.ofNat 64 v.hash) _ by
        simpa only [rspA] using hashA)
    intro i hi
    apply effectT.agrees.byte
    intro component member covered
    simp only [Stages.zeroEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,he⟩ := covered
    all_goals
      refine (RangeApart.offsets (stackPtr a) (len := 8) (b := v.hash) (count := 32)
        ?_ ?_ ?_) j hj i hi he.symm
    all_goals cases v <;> decide
  have frameT := effectT.agrees.memoryWriteFrame
    (zero_writes v a (local_bounds v pre ((rspA.trans rspC).trans rsp)).2)
  have keepC (r : X86.Syntax.Reg) (member : r ∈ ([v.lengthReg,v.blocksReg,v.hashReg] : List X86.Syntax.Reg)) :
      c.regValue r = s.regValue r := by
    apply reg_agrees effectC.agrees
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals cases v <;> simp [Stages.copyEffect, Effect.components, Write.component, Operand.component] <;> decide
  have keepT (r : X86.Syntax.Reg) : t.regValue r = a.regValue r :=
    reg_agrees effectT.agrees r
      (by simp [Stages.zeroEffect, Effect.components, Write.component, Operand.component])
  refine ⟨n+m+k,t,(runC.trans runA).trans runT,readyT,runningT,
    (rspT.trans rspA).trans rspC,
    rbxT.trans ((abiA.1 .rbx (by simp)).trans rbxC),
    stableT.trans ((abiA.1 v.stableReg (by cases v <;> simp <;> decide)).trans stableC),
    mxcsrT.trans (abiA.2.2.1.trans mxcsrC),
    fcwT.trans (abiA.2.2.2.trans fcwC), ?_, effectT.rip,
    (keepT v.lengthReg).trans ((abiA.1 v.lengthReg (by cases v <;> simp <;> decide)).trans ((keepC v.lengthReg (by simp)).trans remainder)),
    (keepT v.blocksReg).trans ((abiA.1 v.blocksReg (by cases v <;> simp <;> decide)).trans ((keepC v.blocksReg (by simp)).trans blocks)),
    ?_, ?_, ?_⟩
  · exact memoryWriteFrame_trans frameC (memoryWriteFrame_trans
      (by simpa only [rspC] using frameA) (by simpa only [rspA,rspC] using frameT))
  · rw [rspT,rspA,rspC]
    exact (keepT v.hashReg).trans ((abiA.1 v.hashReg (by cases v <;> simp <;> decide)).trans ((keepC v.hashReg (by simp)).trans pointer))
  · simpa only [rspT] using hashT
  · have readableT := local_readable v pre runningT
      (((rspT.trans rspA).trans rspC).trans rsp) v.tail 56 (by cases v <;> decide)
    rw [rspT] at readableT
    have bytesT := zero_bytes v effectT readableT
    rw [rspT]
    exact bytesT

end Hkdf.Proofs.Common.StreamPadding.Execution
