import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Defs
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Arithmetic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

macro "batch_scratch_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (apply StoreOk.of_region (b := ($fr).rsp + 8) (len := 1)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         repeat' first | assumption | apply Writable.memStore))

theorem low_merge8 (v : BitVec 8) (x : BitVec 64) :
    (mergeGPR 8 v x).setWidth 8 = v := by
  exact setWidth_mergeGPR8 v x

theorem low32 (x : BitVec 64) : (x.setWidth 32).setWidth 8 = x.setWidth 8 := by bv_omega

theorem low_get8 (v : Value) : (v.get 64).setWidth 8 = v.get 8 :=
  setWidth_get v (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem entry_block (last : Bool) (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout last fr controls).BlockSimulation code .entry := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, setWidth_mergeGPR8, Correction.byte_extend, Correction.low_byte, Correction.widen_low, memLoad_memStore_8]
  all_goals try simp only [setWidth_mergeGPR8, memLoad_memStore_8]
  all_goals try refine_close [scratchRegion, low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, memLoad_memStore_8, BitVec.xor_comm, BitVec.and_comm]
  all_goals try batch_scratch_store fr mem _hcode
  all_goals try bv_omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem selectedDelta_block (last : Bool) (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout last fr controls).BlockSimulation code .selectedDelta := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, setWidth_mergeGPR8, Correction.byte_extend, Correction.low_byte, Correction.widen_low, memLoad_memStore_8]
  all_goals try simp only [memLoad_memStore_8]
  all_goals try refine_close [scratchRegion, low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, memLoad_memStore_8, BitVec.xor_comm, BitVec.and_comm, BitVec.add_comm]
  all_goals try batch_scratch_store fr mem _hcode
  all_goals try bv_omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem selectedFG_block (last : Bool) (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout last fr controls).BlockSimulation code .selectedFG := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, setWidth_mergeGPR8, Correction.byte_extend, Correction.low_byte, Correction.widen_low, memLoad_memStore_8]
  all_goals try simp only [memLoad_memStore_8]
  all_goals try refine_close [scratchRegion, low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, memLoad_memStore_8, BitVec.xor_comm, BitVec.and_comm]
  all_goals try batch_scratch_store fr mem _hcode
  all_goals try bv_omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem selectedUV_block (last : Bool) (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout last fr controls).BlockSimulation code .selectedUV := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, setWidth_mergeGPR8, Correction.byte_extend, Correction.low_byte, Correction.widen_low, memLoad_memStore_8]
  all_goals try simp only [memLoad_memStore_8]
  all_goals try refine_close [scratchRegion, low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, memLoad_memStore_8, BitVec.xor_comm, BitVec.and_comm]
  all_goals try batch_scratch_store fr mem _hcode
  all_goals try bv_omega
set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem selectedQR_block (last : Bool) (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout last fr controls).BlockSimulation code .selectedQR := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, setWidth_mergeGPR8, Correction.byte_extend, Correction.low_byte, Correction.widen_low, memLoad_memStore_8]
  all_goals try simp only [memLoad_memStore_8]
  all_goals try refine_close [scratchRegion, low_get8, low_merge8, low32, next, positiveBit, oddByte, swapByte, maskedF, select, memLoad_memStore_8, BitVec.xor_comm, BitVec.and_comm]
  all_goals try batch_scratch_store fr mem _hcode
  all_goals try bv_omega

set_option maxHeartbeats 600000 in
theorem shift_false_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout false fr controls).BlockSimulation code .shift := by
  refine_intro
  have hs : 1 < snd := by simpa using atom10
  have hdec : (BitVec.ofNat 32 snd - 1).setWidth 64 =
      (BitVec.ofNat 32 (snd - 1)).setWidth 64 := by bv_omega
  have hbranch : (BitVec.ofNat 32 snd - 1 == 0) = false := by
    simp only [Bool.beq_eq_decide_eq, decide_eq_false_iff_not]
    intro hz
    have hv := congrArg BitVec.toNat hz
    have hsmall : snd < 2^32 := by omega
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hv
    change (2^32-1+snd) % 2^32 = 0 at hv
    omega
  refine_uir []
  all_goals refine_lifted [hdec, hbranch, not_true_eq_false]
  all_goals try refine_close [hdec, hbranch, not_true_eq_false]

set_option maxHeartbeats 600000 in
theorem shift_true_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout true fr controls).BlockSimulation code .shift := by
  refine_intro
  have hs : snd = 1 := by simpa using atom10
  subst snd
  refine_uir []
  all_goals refine_lifted [not_true_eq_false]
  all_goals try refine_close []

theorem shift_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout last fr controls).BlockSimulation code .shift := by
  cases last
  · exact shift_false_block code fr controls
  · exact shift_true_block code fr controls

end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
