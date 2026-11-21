import P256.Proofs.Field.Interface
import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Proofs.SecretKeyFromBytes.Scalar
open X86 X86.Machine X86Proofs

theorem MontgomeryAt.memLoad_limb {s : RamState} {address : BitVec 64} {x : Nat}
    (h : MontgomeryAt s address x) (j : Nat) (hj : j < 4) :
    memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 ((x * 2^256 % P256.Spec.Operations.domain.p) / 2^(64*j)) :=
  h.2.memLoad_limb j hj

theorem montgomeryAt_of_memLoad_limbs {s : RamState} {address : BitVec 64} {x : Nat}
    (hx : x < P256.Spec.Operations.domain.p)
    (ha : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (hl : ∀ j < 4, memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 ((x * 2^256 % P256.Spec.Operations.domain.p) / 2^(64*j))) :
    MontgomeryAt s address x :=
  ⟨hx, nat256At_of_memLoad_limbs
    (Nat.lt_trans (Nat.mod_lt _ Montgomery.p_pos) Montgomery.p_lt_radix) ha hl⟩

theorem montgomeryAt_product {s : RamState} {address : BitVec 64} {x y : Nat}
    (h : Nat256At s address (Montgomery.subtractP (Montgomery.reduceFour
      ((x * 2^256 % Montgomery.p) * (y * 2^256 % Montgomery.p))))) :
    MontgomeryAt s address (x * y % Montgomery.p) := by
  rw [Montgomery.subtractP_reduceFour_montgomery_mul] at h
  refine ⟨Nat.mod_lt _ Montgomery.p_pos, ?_⟩
  simpa only [Nat.mod_mul_mod] using h

def readLimbs (s : RamState) (address : BitVec 64) : Limbs :=
  ⟨memLoad s.external address 64, memLoad s.external (address + 8) 64,
    memLoad s.external (address + 16) 64, memLoad s.external (address + 24) 64⟩

theorem readLimbs_toNat {s : RamState} {address : BitVec 64} {x : Nat}
    (h : Nat256At s address x) : (readLimbs s address).toNat = x := by
  have h0 := h.memLoad_limb 0 (by decide)
  have h1 := h.memLoad_limb 1 (by decide)
  have h2 := h.memLoad_limb 2 (by decide)
  have h3 := h.memLoad_limb 3 (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.add_zero] at h0
  change memLoad s.external (address + 8) 64 = BitVec.ofNat 64 (x / 2^64) at h1
  change memLoad s.external (address + 16) 64 = BitVec.ofNat 64 (x / 2^128) at h2
  change memLoad s.external (address + 24) 64 = BitVec.ofNat 64 (x / 2^192) at h3
  rw [readLimbs, h0, h1, h2, h3]
  exact limbs_ofNat_toNat x h.1

theorem nat256At_readLimbs {s : RamState} {address : BitVec 64}
    (ha : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome) :
    Nat256At s address (readLimbs s address).toNat := by
  apply nat256At_of_memLoad_limbs (limbs_toNat_lt _) ha
  intro j hj
  have h0 := (readLimbs s address).l0.isLt
  have h1 := (readLimbs s address).l1.isLt
  have h2 := (readLimbs s address).l2.isLt
  have h3 := (readLimbs s address).l3.isLt
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp only [readLimbs, Limbs.toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.mul_one,
      Nat.pow_zero, Nat.div_one, BitVec.add_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat] at *
    omega

end P256.Proofs.Field
