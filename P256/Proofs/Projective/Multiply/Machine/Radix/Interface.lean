import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Projective.Multiply.Radix.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (d : Nat),
    CalleePre s boundary 0x10b720 32 65 136 →
    Nat256At s (s.regValue .rsi) d →
    ∃ t, CalleeResult s t boundary 65 136 ∧ t.regValue .rax = s.regValue .rdi ∧
      Bytes t.external (s.regValue .rdi) 65
        (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i))

end P256.Proofs.Projective.Multiply.Machine.Radix
