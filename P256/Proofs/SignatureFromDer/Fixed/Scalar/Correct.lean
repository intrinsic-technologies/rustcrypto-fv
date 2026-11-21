import P256.Proofs.SignatureFromDer.Fixed.Scalar.Range
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem scalar_decode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (length : s.regValue .rdx = 32)
    (bytes : (registerRegion s .rsi 32).HasBytes s.external input) :
    ∃ t, CalleeResult s t boundary 40 288 ∧ ScalarResultAt t (s.regValue .rdi) input := by
  obtain ⟨u, decoded⟩ := scalar_decode pre length bytes
  obtain ⟨v, compared⟩ := scalar_range pre decoded
  exact scalar_finish pre compared

end P256.Proofs.SignatureFromDer.Fixed.Scalar
