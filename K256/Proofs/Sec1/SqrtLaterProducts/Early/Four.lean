import K256.Proofs.Sec1.SqrtLaterProducts.Early.Call

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

def offsetsFour : List Word := [0, 8, 16, 24, 32, 80, 88, 96, 104, 112, 120, 128, 136, 192]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageFour {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp)
    (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x1167bf ∨ 0x116bd8 + 8 ≤ sp.toNat) :
    CallTo (lifted := lifted) (squareEntry args mem sp .l116bd8 0x116bd8 3 offsetsFour
      (fun _ _ => True))
      (lifted.program.runBlock (dialect code) ⟨.l1167bf, args, mem⟩) := by
  have haddr : (sp - (8 : BitVec 64)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp]
  subst sp
  final_product_block
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · early_registers
  · early_registers
  · final_product_frame
  · trivial

end K256.Proofs.Sec1.SqrtLaterProducts.Early
