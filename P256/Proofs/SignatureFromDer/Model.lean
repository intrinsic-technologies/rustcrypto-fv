import P256.Spec.Ecdsa
import P256.Proofs.SecretKeyFromBytes.Model

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer

open P256.Spec Standards.SECG.ECC
open P256.Proofs.SecretKeyFromBytes.Encoding

theorem octetsToNat_natToOctets (length value : Nat) :
    Encoding.octetsToNat (Encoding.natToOctets length value) = value % 256 ^ length := by
  induction length generalizing value with
  | zero =>
    rw [show 256 ^ 0 = 1 from rfl, Nat.mod_one]
    have he : Encoding.natToOctets 0 value = .empty := by
      apply ByteArray.ext
      apply Array.eq_empty_of_size_eq_zero
      exact natToOctets_size 0 value
    rw [he]
    rfl
  | succ length ih =>
    rw [natToOctets_succ]
    simp only [Encoding.octetsToNat, ByteArray.data_append, Array.foldl_append]
    change 256 * Encoding.octetsToNat (Encoding.natToOctets length (value / 256)) +
      (UInt8.ofNat (value % 256)).toNat = _

    rw [ih, UInt8.toNat_ofNat', Nat.mod_mod, Nat.pow_succ]
    rw [Nat.mul_comm (256 ^ length) 256, Nat.mod_mul, Nat.add_comm]

theorem encodeFixed_size (value : Nat × Nat) : (Ecdsa.encodeFixed value).size = 64 := by
  simp [Ecdsa.encodeFixed, Operations.encodeSignature, natToOctets_size]

theorem encodeFixed_first (value : Nat × Nat) :
    (Ecdsa.encodeFixed value).extract 0 32 = Encoding.natToOctets 32 value.1 :=
  ByteArray.extract_append_eq_left (by rw [natToOctets_size])

theorem encodeFixed_second (value : Nat × Nat) :
    (Ecdsa.encodeFixed value).extract 32 64 = Encoding.natToOctets 32 value.2 :=
  ByteArray.extract_append_eq_right (by rw [natToOctets_size])
    (by rw [natToOctets_size, natToOctets_size])

theorem decodeSecret_natToOctets {value : Nat} (bound : value < 2 ^ 256) :
    Keys.decodeSecret Operations.domain (Encoding.natToOctets 32 value) =
      if 0 < value ∧ value < Operations.domain.n then some value else none := by
  have width : (Operations.domain.n.log2 + 8) / 8 = 32 := by decide +kernel
  simp only [Keys.decodeSecret, natToOctets_size, width, beq_self_eq_true,
    Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, octetsToNat_natToOctets,
    show (256:Nat)^32 = 2^256 by decide +kernel, Nat.mod_eq_of_lt bound]

theorem decodeSignature_eq {input : ByteArray} (size : input.size = 64) :
    Ecdsa.decodeSignature input =
      if 0 < Arith.uint (input.extract 0 32) ∧
        Arith.uint (input.extract 0 32) < Operations.domain.n ∧
        0 < Arith.uint (input.extract 32 64) ∧
        Arith.uint (input.extract 32 64) < Operations.domain.n then
        some (Arith.uint (input.extract 0 32), Arith.uint (input.extract 32 64)) else none := by
  simp only [Ecdsa.decodeSignature, size, ite_true]
  change (Keys.secretOfBytes (input.extract 0 32)).bind (fun r =>
    (Keys.secretOfBytes (input.extract 32 64)).bind (fun s => some (r,s))) = _
  rw [P256.Proofs.SecretKeyFromBytes.secretOfBytes_eq,
    P256.Proofs.SecretKeyFromBytes.secretOfBytes_eq]
  have first : (input.extract 0 32).size = 32 := by simp [size]
  have second : (input.extract 32 64).size = 32 := by simp [size]
  simp only [first, second, true_and]
  by_cases hr : 0 < Arith.uint (input.extract 0 32) ∧
      Arith.uint (input.extract 0 32) < Operations.domain.n <;>
    by_cases hs : 0 < Arith.uint (input.extract 32 64) ∧
      Arith.uint (input.extract 32 64) < Operations.domain.n <;> simp [hr, hs]

theorem decodeSignature_none_iff {input : ByteArray} (size : input.size = 64) :
    Ecdsa.decodeSignature input = none ↔
      Arith.uint (input.extract 0 32) = 0 ∨
      Operations.domain.n ≤ Arith.uint (input.extract 0 32) ∨
      Arith.uint (input.extract 32 64) = 0 ∨
      Operations.domain.n ≤ Arith.uint (input.extract 32 64) := by
  rw [decodeSignature_eq size]
  split <;> simp_all <;> omega

theorem decodeSignature_none_iff_zero {input : ByteArray} (size : input.size = 64)
    (first : Arith.uint (input.extract 0 32) < Operations.domain.n)
    (second : Arith.uint (input.extract 32 64) < Operations.domain.n) :
    Ecdsa.decodeSignature input = none ↔
      Arith.uint (input.extract 0 32) = 0 ∨ Arith.uint (input.extract 32 64) = 0 := by
  rw [decodeSignature_none_iff size]
  omega

end P256.Proofs.SignatureFromDer
