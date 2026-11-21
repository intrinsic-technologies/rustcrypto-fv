import Base16ct.Spec.Program
import Base16ct.Spec.Base16

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Base16ct.Spec.Base16 Standards.RFC.BaseEncodings

def encodedBytes (input : List UInt8) : List UInt8 :=
  input.flatMap fun b =>
    [Alphabet.base16Lower.character (b.toNat / 16),
      Alphabet.base16Lower.character (b.toNat % 16)]

theorem encodedBytes_length (input : List UInt8) :
    (encodedBytes input).length = 2 * input.length := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [encodedBytes, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

theorem streamBit_cons_shift (b : Nat) (input : List Nat) (p : Nat) :
    streamBit 8 (b :: input) (8 + p) = streamBit 8 input p := by
  simp only [streamBit, show (8 + p) / 8 = p / 8 + 1 by omega,
    show (8 + p) % 8 = p % 8 by omega, List.getD_cons_succ]

theorem regroup_high_nibble (b : UInt8) (input : List Nat) :
    ofBits 4 (fun j => streamBit 8 (b.toNat :: input) j) = b.toNat / 16 := by
  simp only [ofBits, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
  change 2 * (2 * (2 * (b.toNat.testBit 7).toNat + (b.toNat.testBit 6).toNat) +
    (b.toNat.testBit 5).toNat) + (b.toNat.testBit 4).toNat = b.toNat / 16
  simp only [Nat.toNat_testBit]
  have := b.toNat_lt
  omega

theorem regroup_low_nibble (b : UInt8) (input : List Nat) :
    ofBits 4 (fun j => streamBit 8 (b.toNat :: input) (4 + j)) = b.toNat % 16 := by
  simp only [ofBits, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
  change 2 * (2 * (2 * (b.toNat.testBit 3).toNat + (b.toNat.testBit 2).toNat) +
    (b.toNat.testBit 1).toNat) + (b.toNat.testBit 0).toNat = b.toNat % 16
  simp only [Nat.toNat_testBit]
  omega

theorem regroup_cons (b : UInt8) (input : List Nat) (count : Nat) :
    regroup 8 4 (b.toNat :: input) (2 + count) =
      b.toNat / 16 :: b.toNat % 16 :: regroup 8 4 input count := by
  simp only [regroup, List.range_add, List.map_append, List.map_map]
  change ofBits 4 (fun j => streamBit 8 (b.toNat :: input) j) ::
    ofBits 4 (fun j => streamBit 8 (b.toNat :: input) (4 + j)) ::
    (List.range count).map (fun i => ofBits 4 (fun j =>
      streamBit 8 (b.toNat :: input) (4 * (2 + i) + j))) = _
  rw [regroup_high_nibble, regroup_low_nibble]
  congr 2
  apply List.map_congr_left
  intro i _
  congr 1
  funext j
  rw [show 4 * (2 + i) + j = 8 + (4 * i + j) by omega, streamBit_cons_shift]

theorem regroup_eq_flatMap (input : List UInt8) :
    regroup 8 4 (input.map UInt8.toNat) (2 * input.length) =
      input.flatMap (fun b => [b.toNat / 16, b.toNat % 16]) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [List.map_cons, List.length_cons]
    rw [show 2 * (input.length + 1) = 2 + 2 * input.length by omega, regroup_cons, ih]
    rfl

theorem encode_eq_encodedBytes (input : ByteArray) :
    Base16ct.Spec.Base16.lowerEncoder input =
      (encodedBytes input.data.toList).toByteArray := by
  have hcount : Alphabet.base16Lower.encodedLength input.size = 2 * input.size := by
    change (8 * input.size + 4 - 1) / 4 = 2 * input.size
    omega
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [Base16ct.Spec.Base16.lowerEncoder, encode, hcount,
    List.replicate_zero, List.append_nil, List.toList_toArray,
    List.toList_data_toByteArray]
  change (regroup 8 4 (input.data.toList.map UInt8.toNat)
    (2 * input.data.toList.length)).map Alphabet.base16Lower.character =
      encodedBytes input.data.toList
  rw [regroup_eq_flatMap, List.map_flatMap]
  rfl

end Base16ct.Proofs.LowerEncode
