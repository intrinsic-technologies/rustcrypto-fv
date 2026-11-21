import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix.Layout

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxRecDepth 4096

set_option maxHeartbeats 1800000 in
theorem entry_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .entry := by
  refine_intro
  try simp only [initialState] at *
  refine_uir []
  all_goals refine_lifted [initialState]
  all_goals try refine_close [initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom53)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom55)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom57)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom59)

set_option maxHeartbeats 1800000 in
theorem loads_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .loads := by
  refine_intro
  try simp only [initialState] at *
  refine_uir []
  all_goals refine_lifted [initialState]
  all_goals try refine_close [initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom53)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom55)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom57)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom59)

set_option maxHeartbeats 1800000 in
theorem coefficients_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .coefficients := by
  refine_intro
  try simp only [initialState] at *
  refine_uir []
  all_goals refine_lifted [initialState]
  all_goals try refine_close [initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom53)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom55)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom57)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom59)

set_option maxHeartbeats 1800000 in
theorem initialize_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .initialize := by
  refine_intro
  try simp only [initialState] at *
  refine_uir []
  all_goals refine_lifted [initialState]
  all_goals try refine_close [initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom53)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom55)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom57)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom59)

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix
