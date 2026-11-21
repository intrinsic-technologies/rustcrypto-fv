import P256.Proofs.Sec1.Affine.Branches
import P256.Proofs.Sec1.Affine.Compressed
import P256.Proofs.Sec1.Affine.Compact
import P256.Proofs.Sec1.Affine.Uncompressed

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem affine_decode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) :
    ∃ t, CalleeResult s t boundary 80 3360 ∧
      AffineResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes) :=
  affine_decode_of_branches compressed_correct compact_correct uncompressed_correct pre

end P256.Proofs.Sec1.Affine
