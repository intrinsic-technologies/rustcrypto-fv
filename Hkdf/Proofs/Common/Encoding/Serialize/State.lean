import Hkdf.Proofs.Common.Machine.Interfaces
import Hkdf.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Encoding.Serialize

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]

end Hkdf.Proofs.Common.Encoding.Serialize
