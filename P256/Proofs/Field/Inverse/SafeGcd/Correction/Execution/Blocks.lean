import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Basic
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Arithmetic

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

theorem or_zf (x : BitVec 64) : (orFlags x).ZF.getD false = decide (x = 0) := rfl

set_option maxHeartbeats 1200000 in
theorem entry_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .entry := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage0_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage0 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v1181c2, v1181c5, v1181cb, v1181ce, v1181d1, v1181d4, v1181d7, v1181db]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage1_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage1 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v1181ed, v1181f9, v1181fc, v118200, v118203, v118209, v11820c, v11820f, v118212, v118215]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage2_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage2 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v118220, v11822c, v11822f, v118233, v118236, v11823c, v11823f, v118242, v118245, v118248]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage3_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage3 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v118259, v118263, v118266, v11826a, v11826d, v118273, v118276, v118279, v11827c, v11827f]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage4_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage4 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v11828b, v11828e, v118291, v118294]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage5_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage5 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, v1182ac, v1182af, v1182b2, v1182b5, v1182c2, v1182c5, v1182c8, v1182cb, v1182d7, v1182da, v1182dd, v1182e0, v1182ec, v1182ef, v1182f2, v1182f5]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

set_option maxHeartbeats 1200000 in
theorem stage6_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage6 := by
  x86_refine [widen_low,byte_extend, low_byte, or_zf,addSpec_low, setWidth_mergeGPR8, correctedWords]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | correction_stack_store fr mem _hcode | correction_output_store fr mem _hcode

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
