import P256.Proofs.Sec1.Decompress.Correct
import P256.Proofs.Sec1.SquareRoot.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem decompress_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd) :
    ∃ t, CalleeResult s t boundary 80 2592 ∧ AffineResultAt t (s.regValue .rdi)
      (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd) :=
  decompress_correct_of_sqrt (fun _ _ _ hp hx ↦ SquareRoot.field_sqrt_correct hp hx) pre

end P256.Proofs.Sec1.Decompress
