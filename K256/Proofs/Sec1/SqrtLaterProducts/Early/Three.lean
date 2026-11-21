import K256.Proofs.Sec1.SqrtLaterProducts.Early.Call

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

def offsetsThree : List Word := [0, 8, 16, 24, 32, 80, 88, 96, 104, 112, 120, 128, 136, 176, 192, 208, 264]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageThree {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp)
    (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x116316 ∨ 0x116747 + 8 ≤ sp.toNat) :
    CallTo (lifted := lifted) (squareEntry args mem sp .l116747 0x116747 3 offsetsThree
      (fun _ m => memLoad m (sp + 176) 64 = args[13].get 64 ∧
        memLoad m (sp + 208) 64 = args[15].get 64))
      (lifted.program.runBlock (dialect code) ⟨.l116316, args, mem⟩) := by
  have haddr : (sp - (8 : BitVec 64)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp]
  subst sp
  final_product_block
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · early_registers
  · early_registers
  · final_product_frame
  · constructor <;> early_saved_word

end K256.Proofs.Sec1.SqrtLaterProducts.Early
