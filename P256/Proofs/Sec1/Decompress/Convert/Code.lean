import P256.Proofs.Program.Code
import Init.Data.List.Nat.Range

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Spec.Program

set_option maxRecDepth 4096 in
theorem conversion_body_eq :
    Extracted.textBytes.toListFrom 0x8f70 1469 =
      Extracted.textBytes.toListFrom 0x145e0 1469 := by
  decide +kernel

theorem chunked_toListFrom_sub (data : Prelude.Bytes.Chunked)
    (base length offset count : Nat) (h : offset + count ≤ length) :
    ((data.toListFrom base length).drop offset).take count =
      data.toListFrom (base + offset) count := by
  unfold Prelude.Bytes.Chunked.toListFrom
  rw [← List.map_drop, List.drop_range', ← List.map_take,
    List.take_range'_of_length_ge (by omega)]
  simp only [Nat.mul_one]

theorem conversion_slice_eq (offset count : Nat) (h : offset + count ≤ 1469) :
    Extracted.textBytes.toListFrom (0x8f70 + offset) count =
      Extracted.textBytes.toListFrom (0x145e0 + offset) count := by
  have he := congrArg (fun bytes : List UInt8 ↦ (bytes.drop offset).take count)
    conversion_body_eq
  simpa only [chunked_toListFrom_sub _ _ _ _ _ h] using he

end P256.Proofs.Sec1.Decompress.Convert
