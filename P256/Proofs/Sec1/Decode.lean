import P256.Proofs.Sec1.Affine
import P256.Proofs.Sec1.Decode.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre s boundary bytes) :
    ∃ t, CalleeResult s t boundary 80 3680 ∧
      PublicKeyResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePublicKey bytes) :=
  decode_of_affine (fun _ _ _ hp ↦ Affine.affine_decode_correct hp) pre

end P256.Proofs.Sec1.Decode
