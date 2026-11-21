import P256.Proofs.Common.Instructions.AddByte
import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

open P256.Proofs.Common.Instructions.AddByte (add_ff_carry)
open P256.Proofs.Common.Instructions.Setb (setccValue)

namespace P256.Proofs.Common.Field.Montgomery.Schoolbook

open X86 X86.Machine X86.UserProcess X86Proofs

theorem carryBit_eq_ofBool (r : BitVec 64) :
    r.extractLsb' 0 1 = BitVec.ofBool (StatusFlags.ofRFLAGS r).CF := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp [StatusFlags.ofRFLAGS]

theorem savedCarry_add_ff (carry : Bool) :
    (addSpec (BitVec.ofNat 8 carry.toNat) 0xff).2.CF = carry := by
  rw [add_ff_carry]
  cases carry <;> decide +kernel

end P256.Proofs.Common.Field.Montgomery.Schoolbook
