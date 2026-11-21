import P256.Proofs.Common.Memory.Copy.RegisterOps
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

namespace P256.Proofs.Common.Memory

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memcpy_alignment_count (x : BitVec 64) :
    ((-x.setWidth 32) &&& (7 : BitVec 32)).setWidth 64 =
      BitVec.ofNat 64 ((8 - x.toNat % 8) % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (-x.setWidth 32).toNat &&& (2^3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_neg, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  have h32 := Nat.mod_lt x.toNat (show 0 < 4294967296 by decide)
  have h8 := Nat.mod_lt x.toNat (show 0 < 8 by decide)
  have hm := Nat.mod_mod_of_dvd x.toNat (show 8 ∣ 4294967296 by decide)
  have hn := Nat.mod_mod_of_dvd (4294967296 - x.toNat % 4294967296)
    (show 8 ∣ 4294967296 by decide)
  omega

end P256.Proofs.Common.Memory
