import Hkdf.Proofs.Common.StreamPadding.Execution.Control
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls
import Hkdf.Proofs.Common.StreamPadding.Execution.Semantics
import Hkdf.Proofs.Common.StreamPadding.Execution.Transport

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256

attribute [local simp] Variant.lengthReg Variant.lengthIndex Variant.blocksReg
  Variant.blocksIndex Variant.hashReg Variant.hashIndex Variant.remainingReg
  Variant.remainingIndex Variant.stableReg Variant.stableIndex regIndex X86.Syntax.Reg.fin


theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} {message : ByteArray} {hash : Array UInt32} (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .length)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue v.blocksReg = BitVec.ofNat 64 (message.size / 64))
    (hashPointer : s.regValue v.hashReg = stackPtr s + BitVec.ofNat 64 v.hash)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 v.hash) hash)
    (prefixBytes : (⟨(stackPtr s + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ t.RIP = v.pc .exit ∧
      stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue v.stableReg = s.regValue v.stableReg ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control ∧
      MemoryWriteFrame s t (writes v (stackPtr s)) ∧
      HashStateAt t (stackPtr s + BitVec.ofNat 64 v.hash)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits
          (if message.size % 64 < 56 then tailFirst message else tailLast message))) := by
  obtain ⟨lengthFuel,a,lengthRun,readyA,runningA,lengthEffect⟩ :=
    length v pre running rsp rip
  obtain ⟨rspA,rbxA,stableA,mxcsrA,fcwA⟩ := stable_of_agrees_selected v lengthEffect.agrees
    (by cases v <;> simp [Stages.lengthEffect, Effect.components, Write.component, Operand.component] <;> decide)
  have rspOfA : rspOf a = rspOf s := rspA
  have baseA := rspA.trans rsp
  have readableA := local_readable v pre runningA baseA (v.tail+56) 8
    (by cases v <;> decide)
  rw [rspA] at readableA
  have tailA := length_tail_bytes v lengthEffect remainder blocks prefixBytes readableA
  have lengthWords := length_observations v lengthEffect remainder blocks
  have hashA : HashStateAt a (stackPtr s + BitVec.ofNat 64 v.hash) hash := by
    apply Hkdf.Proofs.Common.hashState_of_bytes words
    intro i hi
    apply lengthEffect.agrees.byte
    intro c hc covered
    simp only [Stages.lengthEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,he⟩ := covered
    exact (RangeApart.offsets (stackPtr s) (a := v.tail+56) (len := 8)
      (b := v.hash) (count := 32) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide)) j hj i hi he.symm
  have pointerA : a.regValue v.hashReg = stackPtr a + BitVec.ofNat 64 v.hash := by
    rw [rspA]
    exact (reg_agrees lengthEffect.agrees v.hashReg
      (by cases v <;> simp [Stages.lengthEffect, Effect.components, Write.component, Operand.component] <;> decide)).trans hashPointer
  have frameA := lengthEffect.agrees.memoryWriteFrame
    (length_writes v s (local_bounds v pre rsp).2)
  obtain ⟨copyFuel,b,copyRun,readyB,runningB,copyEffect⟩ := copy v true pre runningA baseA
    (show a.RIP = Stages.copyStart v true from lengthEffect.rip)
  obtain ⟨rspB,rbxB,stableB,mxcsrB,fcwB,frameB⟩ :=
    copy_summary v true copyEffect (local_bounds v pre baseA).2
  have baseB := rspB.trans baseA
  have readableB := local_readable v pre runningB baseB v.scratch 64
    (by cases v <;> decide)
  rw [rspB] at readableB
  have bytesB : (⟨(stackPtr a + BitVec.ofNat 64 v.scratch).toNat,64⟩ : MemoryRegion).HasBytes
      b.external (if message.size % 64 < 56 then tailFirst message else tailLast message) :=
    copy_bytes v true copyEffect (by simpa only [rspOfA] using tailA) readableB
      (fun _ => by simpa only [rspOfA] using lengthWords.1.trans lengthWords.2.symm)
  have hashB := copy_hash v true copyEffect (by simpa only [rspA] using hashA)
  have setup := copyEffect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at setup
  have destination : b.regValue .rdi = stackPtr b + BitVec.ofNat 64 v.hash := by
    rw [rspB]
    exact setup.2.2.2.2.1.trans pointerA
  have source : b.regValue .rsi = stackPtr b + BitVec.ofNat 64 v.scratch := by
    rw [rspB]
    exact setup.2.2.1
  have count : b.regValue .rdx = 1 := setup.2.2.2.1
  obtain ⟨compressFuel,t,compressRun,readyT,runningT,ripT,rspT,abiT,frameT,_,hashT⟩ :=
    compress v true pre runningB baseB copyEffect.rip destination source count
      (by simpa only [rspB] using bytesB) (by simpa only [rspB] using hashB)
  refine ⟨lengthFuel+copyFuel+compressFuel,t,(lengthRun.trans copyRun).trans compressRun,
    readyT,runningT,ripT,rspT.trans (rspB.trans rspA),?_,?_,?_,?_,?_,?_⟩
  · exact (abiT.1 .rbx (by simp)).trans (rbxB.trans rbxA)
  · exact (abiT.1 v.stableReg (by cases v <;> simp <;> decide)).trans (stableB.trans stableA)
  · exact abiT.2.2.1.trans (mxcsrB.trans mxcsrA)
  · exact abiT.2.2.2.trans (fcwB.trans fcwA)
  · apply memoryWriteFrame_trans frameA
    apply memoryWriteFrame_trans
      (show MemoryWriteFrame a b (writes v (stackPtr s)) from by simpa only [rspA] using frameB)
    simpa only [rspB,rspA] using frameT
  · simpa only [rspB,rspA] using hashT

end Hkdf.Proofs.Common.StreamPadding.Execution
