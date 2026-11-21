import K256.Proofs.Sec1.SqrtLaterProducts.Final.Call

namespace K256.Proofs.Sec1.SqrtLaterProducts.Final

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

def offsetsEleven : List Word := [0, 8, 16, 24, 32, 80, 88, 96, 120, 128, 152, 160, 184, 200, 208]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageEleven {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp) (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x118e1a ∨ 0x119258 + 8 ≤ sp.toNat) :
    CallTo (lifted := lifted)
      (CallsSquare args mem sp .l119258 0x119258 offsetsEleven (fun _ => True))
      (lifted.program.runBlock (dialect code) ⟨.l118e1a, args, mem⟩) := by
  have haddr : (sp - (8 : Word)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp]
  subst sp
  final_product_block
  refine ⟨_, _, rfl, rfl, ?_, ?_, trivial⟩
  · final_product_registers
  · final_product_frame

end K256.Proofs.Sec1.SqrtLaterProducts.Final
