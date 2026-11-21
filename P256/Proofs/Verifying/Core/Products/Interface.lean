import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Products

open P256.Proofs.Field X86.Machine X86.UserProcess

abbrev MultiplyPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x113320 280

end P256.Proofs.Verifying.Core.Products
