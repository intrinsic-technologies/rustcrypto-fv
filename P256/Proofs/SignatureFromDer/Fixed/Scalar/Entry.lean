import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Start
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.CopyInput
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Prepare

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scalar_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (length : s.regValue .rdx = 32)
    (bytes : (registerRegion s .rsi 32).HasBytes s.external input) :
    ∃ t, Decode.EntryState s t boundary input := by
  obtain ⟨u, stateU, ripU, sourceU⟩ := Decode.start_correct pre length
  obtain ⟨v, stateV⟩ := Decode.copy_input pre stateU ripU sourceU bytes
  exact Decode.prepare_correct pre stateV

end P256.Proofs.SignatureFromDer.Fixed.Scalar
