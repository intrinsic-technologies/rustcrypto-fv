import K256.Proofs.Common.Invert.LinearCombination.Product
import X86Proofs.Program.Compose
import K256.Proofs.Common.Field.WordOps
import X86Proofs.Instructions.Sbb.Operation
import X86Proofs.Instructions.Adc.Operation
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Correction

namespace K256.Proofs.Common.Invert.ModularShift

export LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

theorem limbs_toNat_lt (a : Limbs) : a.toNat < 2^256 := by
  have h0 := a.l0.isLt
  have h1 := a.l1.isLt
  have h2 := a.l2.isLt
  have h3 := a.l3.isLt
  simp only [K256.Proofs.Common.Invert.LinearCombination.Limbs.toNat]
  omega

abbrev modulusWords : Vector (BitVec 64) 4 := #v[0xfffffffefffffc2f, -1, -1, -1]

abbrev limbs (a : Vector (BitVec 64) 4) : Limbs := ⟨a[0], a[1], a[2], a[3]⟩

abbrev words (a : Limbs) : Vector (BitVec 64) 4 := #v[a.l0, a.l1, a.l2, a.l3]

abbrev prime := limbs modulusWords

theorem prime_pos : 0 < prime.toNat := by decide +kernel

theorem modulus_bound : prime.toNat < 2^256 := limbs_toNat_lt _

end K256.Proofs.Common.Invert.ModularShift
