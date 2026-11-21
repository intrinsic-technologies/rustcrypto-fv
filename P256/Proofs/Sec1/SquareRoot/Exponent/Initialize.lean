import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_initialize [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ t fuel, Advances boundary fuel s t ∧ ExponentLoopState s t x 64 := by
  exact ExponentInitialize.initialize_correct ctx

end P256.Proofs.Sec1.SquareRoot
