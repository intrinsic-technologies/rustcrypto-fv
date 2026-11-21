import P256.Proofs.Sec1.Decode.Validated
import P256.Proofs.Sec1.Decode.Prepare.Prefix
import P256.Proofs.Sec1.Decode.Prepare.Copy
import P256.Proofs.Sec1.Decode.ReturnInput
import P256.Proofs.Sec1.Decode.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_of_affine [Bindings]
    (raw : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      AffineDecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3360 ∧
        AffineResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes))
    {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) :
    ∃ t, CalleeResult s t boundary 80 3680 ∧
      PublicKeyResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePublicKey bytes) := by
  by_cases empty : bytes.size = 0
  · exact decode_empty pre empty
  obtain ready | ⟨a, entry⟩ := validate_positive pre (by omega)
  · exact ready
  obtain ⟨nb, b, ab, stateB⟩ := Prepare.«prefix» pre entry.toFrame entry.rip
    entry.output entry.source entry.length entry.shape
  obtain ⟨c, nc, bc, stateC, outputC, zeroC⟩ := Prepare.prepare_affine_call pre stateB
  obtain ⟨v, cv, _, effect, rawPre⟩ := affine_call pre stateC
  obtain ⟨u, rawResult, rawValue⟩ := raw v boundary bytes rawPre
  obtain ⟨stateU, ripU, valueU⟩ := affine_result pre stateC effect rawResult rawValue
  have outputU : u.regValue .r15 = s.regValue .rdi :=
    (rawResult.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans outputC)
  have zeroU : u.regValue .r12 = 0 :=
    (rawResult.calleeSaved .r12 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 12) (by simp)).trans zeroC)
  obtain ⟨nt, t, ut, stateT, ripT, valueT, _⟩ := result pre stateU ripU outputU zeroU
    valueU entry.shape (affine_prefix stateC effect rawPre rawResult)
  obtain ⟨na, sa⟩ := entry.execution
  obtain ⟨nu, vu⟩ := rawResult.execution
  obtain ⟨final, returned, memory⟩ := finish pre stateT ripT
    ⟨na + nb + nc + 1 + nu + nt, ((((sa.trans ab).trans bc).trans cv).trans vu).trans ut⟩
  refine ⟨final, returned, valueT.of_bytes_eq ?_⟩
  intro i hi
  rw [memory]

end P256.Proofs.Sec1.Decode
