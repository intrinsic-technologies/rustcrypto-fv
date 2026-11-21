import K256.Proofs.Common.Arithmetic.CubicNonzero.Certificate
import K256.Proofs.Common.Arithmetic.CubicNonzero.Fermat
import K256.Proofs.Common.Arithmetic.CubicNonzero.Primality

set_option autoImplicit false

namespace K256.Proofs.Common.Arithmetic

theorem decompressSquare_ne_zero (x : Nat) : decompressSquare x ≠ 0 := by
  apply CubicNonzero.no_root_of_fermat x
  exact CubicNonzero.pow_prime_mod _ x CubicNonzero.prime_secp256k1

end K256.Proofs.Common.Arithmetic
