import K256.Proofs.Verify.Core.Lincomb.Stack

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)


theorem tableCopySetup {fr : Activation} {d : Registers} {n : Ram}
    (sp : d[4].get 64 = workSp fr) (src : d[5].get 64 = slot fr 0x1568)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbbf 3) :
    ∃ x : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10fba8,d,n⟩ =
      .call ⟨.l12a820,x,memStore n (workSp fr - 8) (0x10fbc2 : BitVec 64)⟩
        ⟨.l10fbc2, #v[], rfl, some ⟨64, 0x10fbc2⟩⟩ ∧
      x[4].get 64 = workSp fr - 8 ∧ x[7].get 64 = slot fr 0xbc8 ∧
      x[6].get 64 = slot fr 0x1568 ∧ x[2].get 64 = 1920 ∧ x[12] = ⟨64, 0x12a820⟩ ∧
      ∀ j : Fin Reg.count, j.val ∈ [3,5,13,14,15,22,39,50,51] → x[j] = d[j] := by
  refine ⟨?_, ?call, ?post⟩
  case call =>
    cfg_eval [sp, src, guard]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨j, hj⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem digitCopySetup {fr : Activation} {d : Registers} {n : Ram}
    (sp : d[4].get 64 = workSp fr) (src : d[13].get 64 = slot fr 0x228)
    (target : d[12].get 64 = 0x12a820)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbd2 3) :
    ∃ x : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10fbc2,d,n⟩ =
      .call ⟨.l12a820,x,memStore n (workSp fr - 8) (0x10fbd5 : BitVec 64)⟩
        ⟨.l10fbd5, #v[], rfl, some ⟨64, 0x10fbd5⟩⟩ ∧
      x[4].get 64 = workSp fr - 8 ∧ x[7].get 64 = slot fr 0x1348 ∧
      x[6].get 64 = slot fr 0x228 ∧ x[2].get 64 = 544 ∧ x[12] = d[12] ∧
      ∀ j : Fin Reg.count, j.val ∈ [3,5,13,14,15,22,39,50,51] → x[j] = d[j] := by
  refine ⟨?_, ?call, ?post⟩
  case call =>
    cfg_eval [sp, src, guard, target]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨j, hj⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb
