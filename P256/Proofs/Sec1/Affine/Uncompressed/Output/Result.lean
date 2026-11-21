import P256.Proofs.Sec1.Affine.Uncompressed.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem result_of_fields {t : RamState} {address : BitVec 64} {bytes : ByteArray}
    (size : bytes.size = 65) (tag : bytes.data[0]? = some 4)
    (x : Field.MontgomeryAt t address
      (if valid bytes then canonical (xCoordinate bytes) else 0))
    (y : Field.MontgomeryAt t (address+32)
      (if valid bytes then canonical (yCoordinate bytes) else 0))
    (infinity : t.external[address+64]? = some (if valid bytes then 0 else 1))
    (choice : t.external[address+72]? = some (if valid bytes then 1 else 0)) :
    AffineResultAt t address (Spec.Points.decodePoint bytes) := by
  rw [decodePoint_eq size tag]
  cases h : valid bytes
  · simpa only [h, Bool.false_eq_true, ite_false, AffineResultAt] using choice
  · have bounds := valid_bounds h
    simp only [h, ite_true, canonical_eq bounds.1, canonical_eq bounds.2] at x y
    simp only [h, ite_true] at infinity choice ⊢
    exact ⟨⟨x,y,infinity⟩,choice⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Output
