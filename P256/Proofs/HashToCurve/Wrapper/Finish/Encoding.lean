import P256.Proofs.Sec1Serialize.Interface
import P256.Proofs.Sec1Serialize.Tail.Prepare.Encoding
import P256.Proofs.Sec1.Decode.Header.Length
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.HashToCurve.Wrapper.Finish

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Standards.SECG.ECC Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1.Decode.Header (expectedLength)

def encodingTag : Curve.Point → BitVec 8
  | .infinity => 0
  | .affine _ _ => 4

theorem encodingTag_cases (point : Curve.Point) :
    encodingTag point = 0 ∨ encodingTag point = 4 := by
  cases point <;> simp [encodingTag]

theorem encodedPoint_size (point : Curve.Point) :
    (Sec1Serialize.encodedPoint point).size = 65 := by
  cases point with
  | infinity => rfl
  | affine x y => exact Sec1Serialize.Prepare.encodePoint_uncompressed_size x y

theorem encoded_size (point : Curve.Point) :
    (Points.encode point).size = (expectedLength (encodingTag point)).toNat := by
  cases point with
  | infinity => rfl
  | affine x y => exact Sec1Serialize.Prepare.encodePoint_uncompressed_size x y

theorem encoded_size_le (point : Curve.Point) : (Points.encode point).size ≤ 65 := by
  rw [encoded_size]
  cases point <;> simp [encodingTag, expectedLength]

theorem encoding_capacity (point : Curve.Point) :
    (expectedLength (encodingTag point) ||| 8).toNat = 8 + (Points.encode point).size := by
  rw [encoded_size]
  cases point <;> simp [encodingTag, expectedLength]

theorem encodedPoint_prefix (point : Curve.Point) (i : Nat) (hi : i < (Points.encode point).size) :
    (Sec1Serialize.encodedPoint point).data[i]! = (Points.encode point).data[i]! := by
  cases point with
  | infinity =>
    have index : i = 0 := by change i < 1 at hi; omega
    subst i
    rfl
  | affine x y => rfl

theorem encodedPoint_tag {s : RamState} {address : BitVec 64} {point : Curve.Point}
    (bytes : (MemoryRegion.mk address.toNat 65).HasBytes s.external
      (Sec1Serialize.encodedPoint point)) : memLoad s.external address 8 = encodingTag point := by
  have positive : 0 < (Sec1Serialize.encodedPoint point).data.size := by
    rw [ByteArray.size_data, encodedPoint_size]
    decide
  have atZero := bytes.2 ⟨0, by rw [encodedPoint_size]; decide⟩
  change s.external[BitVec.ofNat 64 (address.toNat + 0)]? =
    some (Sec1Serialize.encodedPoint point).data[0] at atZero
  simp only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at atZero
  cases point with
  | infinity => exact P256.Proofs.Common.Memory.memLoad8_of_byte atZero
  | affine x y =>
    have positiveAffine : 0 < (Points.encode (.affine x y)).data.size := by
      rw [ByteArray.size_data, Sec1Serialize.Prepare.encodePoint_uncompressed_size]
      decide
    have first : (Points.encode (.affine x y)).data[0] = 4 := by
      have value := Sec1Serialize.Prepare.encodePoint_uncompressed_tag x y
      rw [Array.getElem?_eq_getElem (by rw [ByteArray.size_data,
        Sec1Serialize.Prepare.encodePoint_uncompressed_size]; decide)] at value
      exact Option.some.inj value
    change s.external[address]? = some (Points.encode (.affine x y)).data[0] at atZero
    rw [first] at atZero
    exact P256.Proofs.Common.Memory.memLoad8_of_byte atZero

end P256.Proofs.HashToCurve.Wrapper.Finish
