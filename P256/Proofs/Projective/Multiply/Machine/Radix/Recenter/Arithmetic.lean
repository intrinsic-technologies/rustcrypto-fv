import P256.Proofs.Projective.Multiply.Radix.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Proofs.Projective.Multiply.ProjectiveRadix

theorem carry_byte (d i : Nat) :
    ((BitVec.ofNat 8 (nibble d i + carry d i) + 8).sshiftRight 4) =
      BitVec.ofNat 8 (carry d (i+1)) := by
  have bound : nibble d i + carry d i < 17 := by
    have := nibble_lt d i
    have := carry_le_one d i
    omega
  have finite : ∀ a : Fin 17,
      ((BitVec.ofNat 8 a.val + 8).sshiftRight 4) = BitVec.ofNat 8 ((a.val+8)/16) := by
    decide +kernel
  exact finite ⟨_,bound⟩

theorem center_byte (d i : Nat) (hi : i < 64) :
    BitVec.ofNat 8 (nibble d i + carry d i) -
      ((BitVec.ofNat 8 (nibble d i + carry d i) + 8) &&& 240) = digitByte d i := by
  have bound : nibble d i + carry d i < 17 := by
    have := nibble_lt d i
    have := carry_le_one d i
    omega
  have finite : ∀ a : Fin 17,
      BitVec.ofNat 8 a.val - ((BitVec.ofNat 8 a.val + 8) &&& 240) =
        BitVec.ofInt 8 ((a.val : Int) - 16 * ((a.val+8)/16 : Nat)) := by
    decide +kernel
  rw [finite ⟨_,bound⟩]
  simp only [digitByte, digitInt, ite_eq_left hi, centeredDigit, carry, Int.natCast_add]

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
