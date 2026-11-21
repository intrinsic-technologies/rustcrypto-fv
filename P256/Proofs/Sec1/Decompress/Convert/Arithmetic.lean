import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Proofs.Field.Montgomery
open P256.Proofs.SecretKeyFromBytes.Scalar
open X86 X86.Machine X86Proofs

set_option exponentiation.threshold 512 in
theorem raw_product_bound {x : Nat} (bound : x < 2^256) :
    x * (2^512 % p) < p * 2^256 := by
  rw [Nat.mul_comm p]
  exact Nat.mul_lt_mul_of_lt_of_lt bound (Nat.mod_lt _ p_pos)

set_option exponentiation.threshold 512 in
theorem reduced_raw_radixSquared {x : Nat} (bound : x < 2^256) :
    subtractP (reduceFour (x * (2^512 % p))) = x * 2^256 % p := by
  rw [subtractP_reduceFour _ (raw_product_bound bound), Nat.mul_assoc]
  have constant : (2^512 % p) * radixInverse % p = 2^256 % p := by decide +kernel
  rw [← Nat.mul_mod_mod x, constant, Nat.mul_mod_mod]

set_option exponentiation.threshold 512 in
theorem convert_representation {s : RamState} {address : BitVec 64} {x : Nat}
    (bound : x < 2^256)
    (value : Nat256At s address (subtractP (reduceFour (x * (2^512 % p))))) :
    Field.MontgomeryAt s address (x % p) := by
  rw [reduced_raw_radixSquared bound] at value
  refine ⟨Nat.mod_lt _ p_pos, ?_⟩
  simpa only [Nat.mod_mul_mod] using value

end P256.Proofs.Sec1.Decompress.Convert
