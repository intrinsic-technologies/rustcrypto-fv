import P256.Proofs.Verifying.Message.Convert.SelectZ
import P256.Proofs.Verifying.Message.Call.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_core [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (_pre : Pre initial boundary message)
    (state : Selected initial s boundary message x y) :
    ∃ t, Call.Prepared initial t boundary message (.affine x y) := by
  refine ⟨s, state.toFrameState, state.execution, state.rip, ?_, state.digest,
    state.savedSignature, state.savedOutput, state.stackFrame⟩
  refine ⟨state.outputX, ?_, ?_⟩
  · simpa only [lifted, ProjectiveWrapper.Decode.projective, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd] using state.outputY
  · simpa only [lifted, ProjectiveWrapper.Decode.projective, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd] using state.outputZ

end P256.Proofs.Verifying.Message.Convert
