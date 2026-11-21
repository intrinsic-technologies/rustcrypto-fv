import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem call_block (code : CodeMap) (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .entry := by
  refine_intro
  all_goals refine_uir []
  all_goals refine_lifted []
  all_goals first
    | (refine ⟨(), ?_, ?_⟩
       · refine_close []
       · intro uo lo hret _
         obtain ⟨_, ⟨r, _⟩, _⟩ := hret
         cases r)
    | skip
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals modular_stack_store fr mem hcode

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
