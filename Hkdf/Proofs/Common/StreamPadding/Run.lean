import Hkdf.Proofs.Common.StreamPadding.Execution.Prepare
import Hkdf.Proofs.Common.StreamPadding.Execution.First
import Hkdf.Proofs.Common.StreamPadding.Execution.Finish
import Hkdf.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256

theorem run [Bindings] (v : Variant) {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} {message : ByteArray}
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .entry)
    (stream : Common.StreamAt s (stackPtr s + BitVec.ofNat 64 v.tail) message)
    (_size : message.size < 2^61) :
    ∃ t, Result v initial s t boundary message := by
  obtain ⟨n,a,runA,readyA,runningA,rspA,rbxA,rbpA,mxcsrA,fcwA,frameA,
    ripA,remA,blocksA,pointerA,wordsA,bytesA⟩ :=
    Execution.prepare v pre running rsp rip stream
  by_cases small : message.size % 64 < 56
  · have prefixBytes : (⟨(stackPtr a + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
        a.external (finalPrefix message) := by
      rw [← paddedBuffer_prefix message small]
      exact Hkdf.Proofs.Common.Memory.hasBytes_prefix bytesA (by change 56 ≤ 64; decide)
    obtain ⟨m,t,runT,readyT,runningT,ripT,rspT,rbxT,rbpT,mxcsrT,fcwT,frameT,wordsT⟩ :=
      Execution.finish v pre runningA (rspA.trans rsp)
        (by simpa only [small,ite_true] using ripA) remA blocksA pointerA wordsA prefixBytes
    refine ⟨t,⟨⟨n+m,runA.trans runT⟩,readyT,runningT,ripT,rspT.trans rspA,
      rbxT.trans rbxA,rbpT.trans rbpA,mxcsrT.trans mxcsrA,fcwT.trans fcwA,?_,?_⟩⟩
    · exact memoryWriteFrame_trans frameA (by simpa only [rspA] using frameT)
    · rw [compressBlocks_bytePadding_eq,ite_eq_left small]
      simpa only [small,ite_true,rspA] using wordsT
  · have firstBytes : (⟨(stackPtr a + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes
        a.external (tailFirst message) := by
      simpa only [tailFirst,small,ite_false,paddedBuffer]
        using bytesA
    obtain ⟨m,b,runB,readyB,runningB,rspB,rbxB,rbpB,mxcsrB,fcwB,frameB,
      ripB,remB,blocksB,pointerB,wordsB,zeroB⟩ :=
      Execution.first v pre runningA (rspA.trans rsp)
        (by simpa only [small,ite_false] using ripA) remA blocksA pointerA wordsA firstBytes
    have prefixBytes : (⟨(stackPtr b + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
        b.external (finalPrefix message) := by
      simpa only [finalPrefix,small,ite_false] using zeroB
    obtain ⟨k,t,runT,readyT,runningT,ripT,rspT,rbxT,rbpT,mxcsrT,fcwT,frameT,wordsT⟩ :=
      Execution.finish v pre runningB ((rspB.trans rspA).trans rsp) ripB
        remB blocksB pointerB wordsB prefixBytes
    refine ⟨t,⟨⟨n+m+k,(runA.trans runB).trans runT⟩,readyT,runningT,ripT,
      (rspT.trans rspB).trans rspA,
      rbxT.trans (rbxB.trans rbxA),rbpT.trans (rbpB.trans rbpA),
      mxcsrT.trans (mxcsrB.trans mxcsrA),fcwT.trans (fcwB.trans fcwA),?_,?_⟩⟩
    · exact memoryWriteFrame_trans frameA (memoryWriteFrame_trans
        (by simpa only [rspA] using frameB) (by simpa only [rspB,rspA] using frameT))
    · rw [compressBlocks_bytePadding_eq,ite_eq_right small]
      simpa only [small,ite_false,rspB,rspA] using wordsT

end Hkdf.Proofs.Common.StreamPadding
