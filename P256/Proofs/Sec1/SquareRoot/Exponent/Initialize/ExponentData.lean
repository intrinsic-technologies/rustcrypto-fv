import P256.Proofs.Sec1.SquareRoot.Parameters
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_readable {s : RamState} (loaded : ProgramLoaded s)
    {offset : Nat} (bound : offset + 8 ≤ 32) :
    MemReadable s (0x202fb8 + BitVec.ofNat 64 offset) 8 := by
  have hb := exponent_loaded loaded
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2^64)]
    change (0x202fb8 + offset) % 2^64 + 8 ≤ 2^32
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hb.2 (offset+i) (by omega)]
    rfl

theorem exponent_memLoad_word {s : RamState} (loaded : ProgramLoaded s)
    (j : Nat) (bound : j < 4) :
    memLoad s.external (0x202fb8 + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*j)) :=
  (exponent_loaded loaded).memLoad_limb j bound

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
