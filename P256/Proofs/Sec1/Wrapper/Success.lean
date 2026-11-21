import P256.Proofs.Sec1.Wrapper.Accepted
import P256.Proofs.Sec1.Wrapper.Success.Serialize
import P256.Proofs.Sec1.Wrapper.Success.Tail
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem success_from_decoder [bindings : Bindings] {initial s t : RamState}
    {input : ByteArray} {slices : Array Input} {x y : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (entry : DecoderEntry initial s input (returnBoundary initial))
    (result : CalleeResult s t (returnBoundary initial) 80 3680)
    (decoded : PublicKeyResultAt t (s.regValue .rdi) (some (.affine x y))) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      SuccessfulStatus final ∧
      MemoryWriteFrame initial final
        #v[outputRegion publicKeyFromSec1Bytes initial [input], allocatorStateRegion,
          randomSourceRegion, callStack publicKeyFromSec1Bytes initial] ∧
      readOutput publicKeyFromSec1Bytes initial final = .ok (Points.encode (.affine x y)) := by
  have boundary := initial_boundary valid hMachine hBindings
  obtain ⟨_, address, low, outside⟩ := valid.returnAddress
  rw [boundary] at address
  cases address
  obtain ⟨na, a, runA, stateA, ripA, outputA, capacityA, affineA, frameA⟩ :=
    accepted_entry valid entry result decoded
  obtain ⟨nb, b, runB, stateB, ripB, bytesB, frameB, outputB, capacityB⟩ :=
    Success.serialize valid stateA outside ripA affineA
  obtain ⟨_, final, returned, machine, supported, saved, direction, status, frame, bytes⟩ :=
    Success.Tail.correct valid model stateB outside low ripB (capacityB.trans outputA)
      (outputB.trans capacityA) bytesB
  obtain ⟨fuel, unique⟩ := ((runA.trans runB).returns returned).unique_of_boundary boundary
  refine ⟨fuel, final, unique, machine, supported, saved, direction, status, ?_, bytes⟩
  have before := memoryWriteFrame_trans frameA frameB
  intro a outside
  rw [frame a outside]
  apply before a
  intro region member contains
  exact outside region (by simpa [wrapperRegions] using Or.inr member) contains

end P256.Proofs.Sec1.Wrapper
