import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Prepare
import P256.Proofs.HMAC.Finalize.Padding
import P256.Proofs.HMAC.Finalize.OuterBuffer
import P256.Proofs.HMAC.Finalize.Return
import P256.Proofs.HMAC.Finalize.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hmac_finalize_correct [Bindings]
    {initial : RamState} {boundary : ReturnBoundary} {key input : ByteArray}
    (pre : HmacFinalizePre initial boundary key input) :
    ∃ final, HashCalleeResult initial final boundary 672 (Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 key input) := by
  obtain ⟨prepareFuel, prepared, prepareRun, preparedState, prepareRip⟩ := Finalize.prepare pre
  obtain ⟨innerFuel, inner, innerRun, innerState, innerRip, innerFrame⟩ :=
    Finalize.padding_compress false pre.toHashCalleePre preparedState.toBuffered
      prepareRip (inner_remainder_lt key input pre.inputSize)
  have outerState := Finalize.outer_state_of_scratch_frame pre.toHashCalleePre
    preparedState.outer innerFrame
  obtain ⟨bufferFuel, buffered, bufferRun, bufferState, bufferRip⟩ :=
    Finalize.outer_buffer pre innerState outerState innerRip
  have outerSmall :
      (keyPad key 0x5c ++ P256.Spec.Operations.hash (keyPad key 0x36 ++ input)).size % 64 < 56 := by
    rw [ByteArray.size_append, keyPad_size, hash_size]
    decide
  obtain ⟨outerFuel, compressed, outerRun, compressedState, compressedRip, _⟩ :=
    Finalize.padding_compress true pre.toHashCalleePre bufferState bufferRip outerSmall
  obtain ⟨final, result⟩ := Finalize.finalize_return pre.toHashCalleePre compressedState
    compressedRip outerSmall ⟨prepareFuel + innerFuel + bufferFuel + outerFuel,
      ((prepareRun.trans innerRun).trans bufferRun).trans outerRun⟩
  refine ⟨final, ?_⟩
  simpa only [hmacSha256_eq key input (by rw [pre.keySize]; decide)] using result

end P256.Proofs.HMAC
