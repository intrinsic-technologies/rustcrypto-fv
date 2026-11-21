import P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix.Layout

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxRecDepth 4096

set_option maxHeartbeats 1800000 in
theorem entry_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .entry := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  try simp only [Shared.initialState] at *
  refine_uir []
  all_goals refine_lifted [Shared.initialState]
  all_goals try refine_close [Shared.initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

set_option maxHeartbeats 1800000 in
theorem loads_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .loads := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  try simp only [Shared.initialState] at *
  refine_uir []
  all_goals refine_lifted [Shared.initialState]
  all_goals try refine_close [Shared.initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

set_option maxHeartbeats 1800000 in
theorem coefficients_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .coefficients := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega] at *



  try simp only [Shared.initialState] at *
  refine_uir []
  all_goals refine_lifted [Shared.initialState]
  all_goals try refine_close [Shared.initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

set_option maxHeartbeats 1800000 in
theorem scale_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .scale := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega] at *

  try simp only [Shared.initialState] at *
  refine_uir []
  all_goals refine_lifted [Shared.initialState]
  all_goals try refine_close [Shared.initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

set_option maxHeartbeats 1800000 in
theorem initialize_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .initialize := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  try simp only [Shared.initialState] at *
  refine_uir []
  all_goals refine_lifted [Shared.initialState]
  all_goals try refine_close [Shared.initialState]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega


end P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix
