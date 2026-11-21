import P256.Proofs.Verifying.Message.Call.Pre
import P256.Proofs.Verifying.Message.Call.Return
import P256.Proofs.Verifying.Message.Input
import P256.Proofs.Verifying.Message.Finish
import P256.Proofs.Verifying.Message.Convert.Model
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Standards.SECG.ECC SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (key : Curve.Point) : Prop extends Message.Frame initial s where
  execution : ∃ fuel, Advances boundary fuel initial s
  rip : s.RIP = 0x10da4d
  point : ProjectiveAt s (frameBase initial + 1000) (Convert.lifted key)
  digest : (MemoryRegion.mk (frameBase initial + 424).toNat 32).HasBytes
    s.external (Operations.hash message)
  signature : memLoad s.external (frameBase initial + 464) 64 = initial.regValue .r8
  output : memLoad s.external (frameBase initial + 384) 64 = initial.regValue .rdi
  stackFrame : MemoryWriteFrame initial s #v[Stack.region initial 9992]

theorem correct [Bindings] (core : Core.Correct)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    {key : Curve.Point} {r scalarS : Nat} (pre : Pre initial boundary message)
    (input : InputAt initial key r scalarS)
    (valid : Curve.onCurve Operations.domain key = true)
    (rPositive : 0 < r) (rBound : r < Operations.domain.n)
    (sPositive : 0 < scalarS) (sBound : scalarS < Operations.domain.n)
    (state : Prepared initial s boundary message key) :
    ∃ t, CalleeResult initial t boundary 24 9992 ∧
      Core.ResultAt t (initial.regValue .rdi)
        (Ecdsa.verifies key (Operations.hash message) (r, scalarS)) := by
  have signatureInput := input_preserved pre input state.stackFrame
  have coreInput : Core.InputAt initial s (Convert.lifted key)
      (Operations.hash message) r scalarS :=
    ⟨state.point, state.digest, state.signature, state.output,
      signatureInput.2.1, signatureInput.2.2⟩
  obtain ⟨coreFuel, u, coreExecution, result, rip, value⟩ :=
    core (core_pre pre) state.toFrameState state.rip coreInput
      (Convert.lifted_valid key valid) rPositive rBound sPositive sBound
  have value' : Core.ResultAt u (initial.regValue .rdi)
      (Ecdsa.verifies key (Operations.hash message) (r, scalarS)) := by
    simpa only [Convert.lifted_toAffine key valid] using value
  apply finish pre.toCalleePre (after_core result) _ rip value'
  obtain ⟨fuel, execution⟩ := state.execution
  exact ⟨fuel + coreFuel, execution.trans coreExecution⟩

end P256.Proofs.Verifying.Message.Call
