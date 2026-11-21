import Sha2.Proofs.Common.Machine.Interfaces
import Sha2.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace Sha2.Proofs.Common.Encoding.Serialize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]

end Sha2.Proofs.Common.Encoding.Serialize
