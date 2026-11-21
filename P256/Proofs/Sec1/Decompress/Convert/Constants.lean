import P256.Proofs.Field.Interface
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem modulus_at {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x202d88 P256.Spec.Operations.domain.p := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202d88 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (P256.Spec.Operations.domain.p / 256^i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

set_option exponentiation.threshold 512 in
theorem radixSquared_at {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x202dc8 (2^512 % P256.Spec.Operations.domain.p) := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202dc8 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat ((2^512 % P256.Spec.Operations.domain.p) / 256^i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

theorem constant_in_program (address : BitVec 64)
    (addressEq : address = 0x202d88 ∨ address = 0x202dc8) (i : Nat) (bound : i < 32) :
    InProgram (address + BitVec.ofNat 64 i) := by
  have inside : ∀ k : Fin 2, ∀ i : Fin 32,
      (Extracted.programSections.fetchByte
        ((#v[0x202d88, 0x202dc8] : Vector (BitVec 64) 2)[k] +
          BitVec.ofNat 64 i.val)).isSome = true := by decide +kernel +revert
  rcases addressEq with rfl | rfl
  · exact Option.isSome_iff_exists.mp (inside 0 ⟨i, bound⟩)
  · exact Option.isSome_iff_exists.mp (inside 1 ⟨i, bound⟩)

theorem constant_region_bounded {address : BitVec 64}
    (addressEq : address = 0x202d88 ∨ address = 0x202dc8) :
    (MemoryRegion.mk address.toNat 32).Bounded := by
  rcases addressEq with rfl | rfl <;> unfold MemoryRegion.Bounded <;> decide +kernel

theorem constant_region_inProgram {address a : BitVec 64}
    (addressEq : address = 0x202d88 ∨ address = 0x202dc8)
    (member : (MemoryRegion.mk address.toNat 32).Contains a.toNat) : InProgram a := by
  have lower : address.toNat ≤ a.toNat := member.1
  have upper : a.toNat < address.toNat + 32 := member.2
  have eq : address + BitVec.ofNat 64 (a.toNat - address.toNat) = a := by
    calc
      address + BitVec.ofNat 64 (a.toNat - address.toNat) =
          BitVec.ofNat 64 (address.toNat + (a.toNat - address.toNat)) := by
        rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = a := by rw [Nat.add_sub_of_le lower, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← eq]
  exact constant_in_program address addressEq _ (by omega)

theorem constant_region_allocated {s : RamState} {address : BitVec 64}
    (loaded : ProgramLoaded s)
    (addressEq : address = 0x202d88 ∨ address = 0x202dc8) :
    (MemoryRegion.mk address.toNat 32).Allocated s.external := by
  intro a member
  obtain ⟨byte, found⟩ := constant_region_inProgram addressEq member
  exact ⟨byte, loaded _ _ found⟩

theorem constant_region_disjoint {address : BitVec 64} {region : MemoryRegion}
    (addressEq : address = 0x202d88 ∨ address = 0x202dc8)
    (avoids : region.Avoids (fun a ↦ InProgram a ∨ InPageTables a)) :
    (MemoryRegion.mk address.toNat 32).Disjoint region := by
  intro a member overlap
  have bound : address.toNat + 32 < 2^32 := constant_region_bounded addressEq
  have upper : a < address.toNat + 32 := member.2
  have eq : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact avoids (BitVec.ofNat 64 a) (by simpa only [eq] using overlap)
    (.inl (constant_region_inProgram addressEq (by simpa only [eq] using member)))

end P256.Proofs.Sec1.Decompress.Convert
