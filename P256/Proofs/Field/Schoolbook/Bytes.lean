import P256.Proofs.Field.Schoolbook.Arithmetic
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)

open X86 X86.Machine X86.UserProcess X86Proofs

def limbsOfNat (x : Nat) : Vector Nat 4 :=
  #v[x % wordBase, x / wordBase % wordBase,
    x / wordBase^2 % wordBase, x / wordBase^3 % wordBase]

theorem limbsOfNat_lt (x : Nat) (i : Fin 4) : (limbsOfNat x)[i] < wordBase := by
  finite_cases i <;> exact Nat.mod_lt _ (by decide)

theorem packFour_limbsOfNat {x : Nat} (hx : x < 2^256) :
    packFour (limbsOfNat x) = x := by
  calc
    _ = (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk
        (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2^64))
        (BitVec.ofNat 64 (x / 2^128)) (BitVec.ofNat 64 (x / 2^192))).toNat := by
      dsimp [packFour, limbsOfNat, wordBase,
        P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
      simp only [BitVec.toNat_ofNat]
      omega
    _ = x := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_ofNat_toNat x hx

set_option exponentiation.threshold 512 in
theorem packEight_digit (v : Vector Nat 8) (hv : ∀ i : Fin 8, v[i] < wordBase)
    (j : Nat) (hj : j < 8) :
    packEight v / 2^(64*j) % wordBase = v[j] := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  change v[0] < wordBase at h0
  change v[1] < wordBase at h1
  change v[2] < wordBase at h2
  change v[3] < wordBase at h3
  change v[4] < wordBase at h4
  change v[5] < wordBase at h5
  change v[6] < wordBase at h6
  change v[7] < wordBase at h7
  have hidx : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hidx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [packEight, wordBase, Nat.reduceMul, Nat.reducePow, Nat.div_one] at *
  all_goals omega

theorem bytes_of_memLoad_packEight {s : RamState} {address : BitVec 64}
    (v : Vector Nat 8) (hv : ∀ i : Fin 8, v[i] < wordBase)
    (ha : ∀ i < 64, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (hl : ∀ j (hj : j < 8), memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (v[j]'hj)) :
    Bytes s.external address 64 (fun i => UInt8.ofNat (packEight v / 256^i % 256)) := by
  intro i hi
  have hi8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj : i / 8 < 8 := by omega
  have hb : Bytes s.external (address + BitVec.ofNat 64 (8 * (i / 8))) 8
      (storedByte (memLoad s.external (address + BitVec.ofNat 64 (8 * (i / 8))) 64)) := by
    apply Bytes.of_memLoad (n := 64)
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ha _ (by omega)
  have he := hb (i % 8) hi8
  have hd : BitVec.ofNat 64 v[i/8] = BitVec.ofNat 64 (packEight v / 2^(64*(i/8))) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [packEight_digit v hv _ hj]
    exact Nat.mod_eq_of_lt (hv ⟨i/8,hj⟩)
  rw [hl _ hj, hd, P256.Proofs.ReadBe.storedByte_ofNat64 _ _ hi8, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (i / 8) + i % 8 = i by omega] at he
  have hp : 256 ^ i = 2 ^ (64 * (i / 8)) * 256 ^ (i % 8) := by
    conv => lhs; rw [show i = 8 * (i / 8) + i % 8 by omega]
    rw [Nat.pow_add]
    congr 1
    rw [show (256 : Nat) = 2^8 by decide +kernel, ← Nat.pow_mul]
    congr 1
    omega
  simpa only [hp, Nat.div_div_eq_div_mul] using he

end P256.Proofs.Field.Schoolbook
