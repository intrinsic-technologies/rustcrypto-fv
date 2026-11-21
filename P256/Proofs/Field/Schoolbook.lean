import P256.Proofs.Field.Schoolbook.Return
import P256.Proofs.Field.Schoolbook.Body
import P256.Proofs.Field.Schoolbook.Inputs
import P256.Proofs.Field.Schoolbook.ProductInputs
import P256.Proofs.Field.Schoolbook.LowerSums.Output

set_option autoImplicit false

open P256.Proofs.Field.Schoolbook (body entry_inputs execution_context finish limbsOfNat limbsOfNat_lt lower_left_inputs lower_sums_inputs lower_sums_output nat256_limb_toNat outputLimbs packFour_limbsOfNat upperProducts_inputs upper_sums_output)
open P256.Proofs.Program (CalleeResult)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.Field.Schoolbook

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem schoolbook_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {a b : Nat} (hpre : SchoolbookPre s boundary)
    (ha : Nat256At s (s.regValue .rsi) a) (hb : Nat256At s (s.regValue .rcx) b) :
    ∃ t, CalleeResult s t boundary 64 136 ∧
      Bytes t.external (s.regValue .rdi) 64
        (fun i => UInt8.ofNat ((a*b) / 256^i % 256)) := by
  obtain ⟨entry, ctx⟩ := execution_context hpre
  obtain ⟨p, lo, up, l, m, u, ps, los, us, hp, hlo, hup, hl, hm, hu, rip⟩ := body ctx
  obtain ⟨v, result, output⟩ := finish us rip
  have he : packEight ((outputLimbs u).map BitVec.toNat) = a*b := by
    rw [upper_sums_output hl hm hu]
    obtain ⟨left, right⟩ := entry_inputs ctx ha hb
    obtain ⟨hr, hq, hpp⟩ := upperProducts_inputs hup
    have fields := lower_sums_inputs hp hlo
    obtain ⟨a2, a3⟩ := lower_left_inputs ps los hp hlo ha
    have row := lower_sums_output hp hlo
    dsimp only at hq hpp row
    rw [hr, row, hq, hpp]
    have s64 : (Operand.mem (rspOf lo+64) : Operand 64).read lo =
        (Operand.mem ((Operand.reg 1 : Operand 64).read entry) : Operand 64).read entry := fields.stack64
    have s72 : (Operand.mem (rspOf lo+72) : Operand 64).read lo =
        (Operand.mem ((Operand.reg 1 : Operand 64).read entry+8#64) : Operand 64).read entry := fields.stack72
    have s40 : (Operand.mem (rspOf lo+40) : Operand 64).read lo =
        (Operand.mem ((Operand.reg 1 : Operand 64).read entry+16#64) : Operand 64).read entry := fields.stack40
    have s56 : (Operand.mem (rspOf lo+56) : Operand 64).read lo =
        (Operand.mem ((Operand.reg 1 : Operand 64).read entry+24#64) : Operand 64).read entry := fields.stack56
    simp only [s64, s72, s40, s56, fields.r14, fields.rbx, a2, a3]
    have la0 := nat256_limb_toNat left 0 (by decide)
    have la1 := nat256_limb_toNat left 1 (by decide)
    have lb0 := nat256_limb_toNat right 0 (by decide)
    have lb1 := nat256_limb_toNat right 1 (by decide)
    have lb2 := nat256_limb_toNat right 2 (by decide)
    have lb3 := nat256_limb_toNat right 3 (by decide)
    change (memLoad entry.external ((Operand.reg 6 : Operand 64).read entry+0#64) 64).toNat = _ at la0
    change (memLoad entry.external ((Operand.reg 1 : Operand 64).read entry+0#64) 64).toNat = _ at lb0
    rw [BitVec.add_zero] at la0 lb0
    change ((Operand.mem ((Operand.reg 6 : Operand 64).read entry) : Operand 64).read entry).toNat = _ at la0
    change ((Operand.mem ((Operand.reg 6 : Operand 64).read entry+8#64) : Operand 64).read entry).toNat = _ at la1
    change ((Operand.mem ((Operand.reg 1 : Operand 64).read entry) : Operand 64).read entry).toNat = _ at lb0
    change ((Operand.mem ((Operand.reg 1 : Operand 64).read entry+8#64) : Operand 64).read entry).toNat = _ at lb1
    change ((Operand.mem ((Operand.reg 1 : Operand 64).read entry+16#64) : Operand 64).read entry).toNat = _ at lb2
    change ((Operand.mem ((Operand.reg 1 : Operand 64).read entry+24#64) : Operand 64).read entry).toNat = _ at lb3
    simp only [la0, la1, lb0, lb1, lb2, lb3]
    have product := schoolbookLimbs_correct (limbsOfNat a) (limbsOfNat b)
      (limbsOfNat_lt a) (limbsOfNat_lt b)
    rw [packFour_limbsOfNat ha.1, packFour_limbsOfNat hb.1] at product
    simpa [schoolbookLimbs, limbsOfNat, Nat.mul_comm] using product
  exact ⟨v, result, by simpa only [he] using output⟩

end P256.Proofs.Field.Schoolbook
