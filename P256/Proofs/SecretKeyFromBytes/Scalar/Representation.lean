import P256.Proofs.SecretKeyFromBytes.Arithmetic
import X86Proofs.Program.ReadWrite.Bytes
import P256.Proofs.ReadBe.Input

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Scalar

open X86 X86.Machine X86Proofs

def Nat256At (s : RamState) (address : BitVec 64) (x : Nat) : Prop :=
  x < 2^256 ∧ ∀ i < 32, s.external[address + BitVec.ofNat 64 i]? =
    some (UInt8.ofNat (x / 256^i % 256))

theorem Nat256At.limbBytes {s : RamState} {address : BitVec 64} {x : Nat}
    (h : Nat256At s address x) (j : Nat) (hj : j < 4) :
    Bytes s.external (address + BitVec.ofNat 64 (8*j)) 8
      (storedByte (BitVec.ofNat 64 (x / 2^(64*j)))) := by
  intro i hi
  rw [P256.Proofs.ReadBe.storedByte_ofNat64 _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have he : 256 ^ (8*j+i) = 2^(64*j) * 256^i := by
    rw [Nat.pow_add]
    congr 1
    rw [show (256 : Nat) = 2^8 by decide +kernel, ← Nat.pow_mul]
    congr 1
    omega
  simpa only [he, Nat.div_div_eq_div_mul] using h.2 (8*j+i) (by omega)

theorem Nat256At.memLoad_limb {s : RamState} {address : BitVec 64} {x : Nat}
    (h : Nat256At s address x) (j : Nat) (hj : j < 4) :
    memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (x / 2^(64*j)) :=
  (h.limbBytes j hj).memLoad (by decide) (by decide)

theorem nat256At_of_memLoad_limbs {s : RamState} {address : BitVec 64} {x : Nat}
    (hx : x < 2^256)
    (ha : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (hl : ∀ j < 4, memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (x / 2^(64*j))) : Nat256At s address x := by
  refine ⟨hx, ?_⟩
  intro i hi
  have hi8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj : i / 8 < 4 := by omega
  have hb : Bytes s.external (address + BitVec.ofNat 64 (8 * (i / 8))) 8
      (storedByte (memLoad s.external (address + BitVec.ofNat 64 (8 * (i / 8))) 64)) := by
    apply Bytes.of_memLoad (n := 64)
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ha _ (by omega)
  have he := hb (i % 8) hi8
  rw [hl _ hj, P256.Proofs.ReadBe.storedByte_ofNat64 _ _ hi8, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (i / 8) + i % 8 = i by omega] at he
  have hp : 256 ^ i = 2 ^ (64 * (i / 8)) * 256 ^ (i % 8) := by
    conv => lhs; rw [show i = 8 * (i / 8) + i % 8 by omega]
    rw [Nat.pow_add]
    congr 1
    rw [show (256 : Nat) = 2^8 by decide +kernel, ← Nat.pow_mul]
    congr 1
    omega
  simpa only [hp, Nat.div_div_eq_div_mul] using he

end P256.Proofs.SecretKeyFromBytes.Scalar
