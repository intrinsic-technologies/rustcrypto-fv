import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open P256.Proofs.Field X86.Machine X86.UserProcess

abbrev MultiplyPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x113040 280

abbrev BarrettPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x112840 112

end P256.Proofs.Scalar.Multiply
