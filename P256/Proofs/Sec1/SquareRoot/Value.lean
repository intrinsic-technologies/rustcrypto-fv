import P256.Proofs.Sec1.SquareRoot.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open Prelude X86 X86.Machine X86.UserProcess
open P256.Spec

abbrev candidate (x : Nat) : Nat :=
  Standards.SECG.ECC.Curve.powMod Operations.domain.p x sqrtExponent

theorem result_of_selected {s : RamState} {address : BitVec 64} {x : Nat}
    (hx : x < Operations.domain.p)
    (value : Field.MontgomeryAt s address
      (if candidate x * candidate x % Operations.domain.p = x then candidate x else 0))
    (valid : s.external[address + 32]? =
      some (if candidate x * candidate x % Operations.domain.p = x then 1 else 0)) :
    SquareRootResultAt s address x := by
  unfold SquareRootResultAt Operations.sqrtMod Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4
  rw [Nat.mod_eq_of_lt hx]
  change (match (if candidate x * candidate x % Operations.domain.p == x then
    some (candidate x) else none) with
    | some root => Field.MontgomeryAt s address root ∧ s.external[address + 32]? = some 1
    | none => Field.MontgomeryAt s address 0 ∧ s.external[address + 32]? = some 0)
  by_cases h : candidate x * candidate x % Operations.domain.p = x
  · simpa only [h, beq_self_eq_true, Bool.true_eq, ↓reduceIte] using And.intro value valid
  · simpa only [beq_iff_eq, h, ↓reduceIte] using And.intro value valid

end P256.Proofs.Sec1.SquareRoot
