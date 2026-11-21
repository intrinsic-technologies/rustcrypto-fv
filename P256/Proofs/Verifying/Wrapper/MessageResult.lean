import P256.Proofs.Verifying.Wrapper.MessageEntry
import P256.Proofs.Verifying.Wrapper.CalleeReturn

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

structure Verified [Bindings] (initial s : RamState) (accepted : Bool) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x1031e9
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  result : Core.ResultAt s (stackPtr initial-208) accepted

theorem verify_message [Bindings] (messageCorrect : Message.Correct)
    {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point} {r scalarS : Nat}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : SignatureReady initial s point r scalarS)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (valid : Curve.onCurve Operations.domain point = true) (nonidentity : point ≠ .infinity)
    (rPositive : 0 < r) (rBound : r < Operations.domain.n)
    (sPositive : 0 < scalarS) (sBound : scalarS < Operations.domain.n) :
    ∃ u, Verified initial u (Ecdsa.verifies point (Operations.hash message) (r,scalarS)) := by
  obtain ⟨a,t,stateA,outputA,capacityA,pre,input,output,sp,ret,ag,frameAT,frameT,n,run⟩ :=
    message_entry call state outside
  obtain ⟨u,callee,result⟩ := messageCorrect pre input valid nonidentity
    rPositive rBound sPositive sBound
  have frameTU := callee.stack_frame (savedBytes := 40) call.stackAvailable.1 sp output
    (by decide) (by decide) (by decide) (by decide)
  have stateU := stateA.after_callee call.stackAvailable.1 ag frameAT
    (by simp [messageCallComponents]) sp callee frameTU
  obtain ⟨nc,inner⟩ := callee.execution
  refine ⟨u,stateU,⟨n+nc,run.trans inner⟩,
    memoryWriteFrame_trans frameT (work_frame call.stackAvailable.1 frameTU),
    callee.rip.trans ret,?_,?_,?_⟩
  · exact (callee.calleeSaved .r12 (by simp)).trans
      ((ag.read (n := 64) (r := 12) (by simp [messageCallComponents])).trans outputA)
  · exact (callee.calleeSaved .r13 (by simp)).trans
      ((ag.read (n := 64) (r := 13) (by simp [messageCallComponents])).trans capacityA)
  · simpa only [output] using result

end P256.Proofs.Verifying.Wrapper
