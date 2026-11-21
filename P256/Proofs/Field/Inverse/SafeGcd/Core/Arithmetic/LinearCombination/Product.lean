import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Support
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.ProductArithmetic
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Signed

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86Proofs
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

def leftWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v1b111e p).1, (v1b1165 p).1, (v1b1168 p).1, (v1b116b p).1, (v1b116e p).1]

def rightWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v1b1175 p).1, (v1b11b3 p).1, (v1b11b8 p).1, (v1b11c5 p).1, (v1b11c8 p).1]

theorem adc_low (a b : BitVec 64) (c : Bool) :
    (Common.Instructions.Carry.adcSpec a b (BitVec.ofBool c)).1 =
      (X86Proofs.adcSpec c a b).1 := by
  simp only [Common.Instructions.Carry.adcSpec, BitVec.toNat_ofBool,
    ofInt_add_add_toNat, X86Proofs.adcSpec]

theorem adc_cf (a b : BitVec 64) (c : Bool) :
    (Common.Instructions.Carry.adcSpec a b (BitVec.ofBool c)).2.CF =
      (X86Proofs.adcSpec c a b).2.CF := by
  simp only [Common.Instructions.Carry.adcSpec, BitVec.toNat_ofBool,
    ofInt_add_add_toNat, X86Proofs.adcSpec, ne_eq, natCast_eq_add_add]

theorem leftWords_product (p : Inputs) :
    wideValue (leftWords p) = (v1b1106 p).toNat * packFour (p.a.map BitVec.toNat) := by
  simpa only [leftWords, wideValue, packFive, packFour, Vector.getElem_map,
    Vector.getElem_mk, Array.reduceGetElem, v1b111e, v1b1130, v1b1145, v1b1158,
    v1b1165, v1b1168, v1b116b, v1b116e, mulResult_fst,
    Support.mulResult_snd, adc_low, adc_cf] using
    product_limbs (v1b1106 p) p.a[0] p.a[1] p.a[2] p.a[3]

theorem rightWords_product (p : Inputs) :
    wideValue (rightWords p) = (v1b1162 p).toNat * packFour (p.b.map BitVec.toNat) := by
  simpa only [rightWords, wideValue, packFive, packFour, Vector.getElem_map,
    Vector.getElem_mk, Array.reduceGetElem, v1b1175, v1b1185, v1b1194, v1b11af,
    v1b11b3, v1b11b8, v1b11c5, v1b11c8, mulResult_fst,
    Support.mulResult_snd, adc_low, adc_cf] using
    product_limbs (v1b1162 p) p.b[0] p.b[1] p.b[2] p.b[3]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
