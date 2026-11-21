import Hkdf.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Machine

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stackRegion_contains_sub {s : RamState} {reserve offset len : Nat}
    (hReserve : Stack.NoUnderflow s reserve) (hOffset : offset ≤ reserve)
    (hLen : len ≤ offset) {address : BitVec 64}
    (hCover : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (Stack.region s reserve).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCover
  have hsp := (stackPtr s).isLt
  change reserve ≤ (stackPtr s).toNat at hReserve
  have ho : offset < 2^64 := by omega
  have hsub : (BitVec.ofNat 64 offset) ≤ stackPtr s := by
    simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho] using
      Nat.le_trans hOffset hReserve
  have hi64 : i < 2^64 := by omega
  have hsum : (stackPtr s).toNat - offset + i < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hsub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
    Nat.mod_eq_of_lt hsum]
  change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset + i ∧
    (stackPtr s).toNat - offset + i < (stackPtr s).toNat - reserve +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - reserve))
  omega

end Hkdf.Proofs.Common.Machine
