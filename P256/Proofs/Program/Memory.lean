import P256.Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace P256.Proofs.Program

open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Spec.Program.Routines

theorem stackPtr_eq_regValue_rsp (s : RamState) : stackPtr s = s.regValue .rsp := rfl

theorem stack_region_end (s : RamState) (reserve : Nat) :
    (Stack.region s reserve).start + (Stack.region s reserve).size =
      (stackPtr s).toNat + 8 := by
  change (s.regValue .rsp).toNat - reserve +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - reserve)) =
      (s.regValue .rsp).toNat + 8
  omega

theorem memoryRegion_contains_add {region : MemoryRegion} {addr : BitVec 64} {len i : Nat}
    (hbound : region.Bounded) (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) (hi : i < len) :
    region.Contains (addr + BitVec.ofNat 64 i).toNat := by
  have hb : region.start + region.size < 2^32 := hbound
  have ha : (addr + BitVec.ofNat 64 i).toNat = addr.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
  rw [ha]
  exact ⟨by omega, by omega⟩

theorem memoryRegion_memReadable {s : RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (hbound : region.Bounded)
    (hmem : region.Allocated s.external) (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) : MemReadable s addr len := by
  refine ⟨by have : region.start + region.size < 2^32 := hbound; omega, ?_⟩
  intro i hi
  obtain ⟨byte, hb⟩ := hmem _ (memoryRegion_contains_add hbound hstart hend hi)
  simp only [hb, Option.isSome_some]

theorem tables_interval_of_not_reserved {addr : BitVec 64} {len : Nat}
    (hpos : 0 < len) (hlow : addr.toNat + len ≤ 2^32)
    (havoid : ∀ i < len, ¬ PageTableReserved (addr + BitVec.ofNat 64 i)) :
    addr.toNat + len ≤ 0x1000 ∨ 0x3000 ≤ addr.toNat := by
  by_cases hbefore : addr.toNat + len ≤ 0x1000
  · exact .inl hbefore
  · right
    apply Nat.le_of_not_lt
    intro hafter
    let i := 0x1000 - addr.toNat
    have hi : i < len := by dsimp [i]; omega
    have h := havoid i hi
    apply h
    change 0x1000 ≤ (addr + BitVec.ofNat 64 i).toNat ∧
      (addr + BitVec.ofNat 64 i).toNat < 0x3000
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + i < 2^64 by omega)]
    dsimp [i]
    omega

end P256.Proofs.Program
