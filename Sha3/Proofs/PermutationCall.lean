import Sha3.Proofs.Memory

namespace Sha3.Proofs

open X86 X86.Machine Prelude Sha3.Spec.Program

theorem stackRegion_nested {initial s : RamState} {outer offset inner : Nat}
    (houter : Stack.NoUnderflow initial outer) (hsize : offset + inner ≤ outer)
    (hsp : s.regValue .rsp = initial.regValue .rsp - BitVec.ofNat 64 offset)
    {address : Nat} (haddress : (Stack.region s inner).Contains address) :
    (Stack.region initial outer).Contains address := by
  have hnat : (s.regValue .rsp).toNat = (initial.regValue .rsp).toNat - offset := by
    rw [hsp]
    exact stack_sub_toNat houter (by omega)
  change outer ≤ (initial.regValue .rsp).toNat at houter
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at haddress ⊢
  rw [hnat] at haddress
  constructor <;> omega

theorem stackValid_nested {initial s : RamState} {outer offset inner : Nat}
    (hstack : Stack.Valid initial outer) (hsize : offset + inner ≤ outer)
    (halign : offset % 16 = 0)
    (hsp : s.regValue .rsp = initial.regValue .rsp - BitVec.ofNat 64 offset)
    (hgrows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (s.external[address]?).isSome) : Stack.Valid s inner := by
  have hnat : (s.regValue .rsp).toNat = (initial.regValue .rsp).toNat - offset := by
    rw [hsp]
    exact stack_sub_toNat hstack.2.2.1 (by omega)
  have hbottom : outer ≤ (initial.regValue .rsp).toNat := hstack.2.2.1
  have hbound := hstack.1
  have hmod := hstack.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
      userAddressLimit] at hbound ⊢
    rw [hnat]
    omega
  · intro address haddress
    have ha := hstack.2.1 address (stackRegion_nested hstack.2.2.1 hsize hsp haddress)
    exact Option.isSome_iff_exists.mp (hgrows address (Option.isSome_iff_exists.mpr ha))
  · change inner ≤ (s.regValue .rsp).toNat
    rw [hnat]
    omega
  · change (s.regValue .rsp).toNat % 16 = 8
    change (initial.regValue .rsp).toNat % 16 = 8 at hmod
    rw [hnat]
    omega

end Sha3.Proofs
