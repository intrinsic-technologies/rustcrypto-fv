import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open X86 X86.Machine

abbrev FrameState [Bindings] (s t : RamState) (stackOffset : BitVec 64 := 152) :=
  Program.ScalarFrame.FrameState s t 40 288 stackOffset

end P256.Proofs.SignatureFromDer.Fixed.Scalar
