import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 1200000 in
theorem entry_block (path : Path) (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout path last fr controls).BlockSimulation code .entry := by
  cases path <;>
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem odd_swap_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .swap last fr controls).BlockSimulation code .odd := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem odd_add_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .add last fr controls).BlockSimulation code .odd := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem even_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .even last fr controls).BlockSimulation code .even := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem swap_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .swap last fr controls).BlockSimulation code .swap := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem add_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .add last fr controls).BlockSimulation code .add := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem join_even_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .even last fr controls).BlockSimulation code .join := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 1200000 in
theorem join_add_block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .add last fr controls).BlockSimulation code .join := by
  refine_intro
  all_goals simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals refine_uir []
  all_goals refine_lifted [not_true_eq_false, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_even_false_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .even false fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hdec : (BitVec.ofNat 32 snd - 1).setWidth 64 =
      (BitVec.ofNat 32 (snd - 1)).setWidth 64 := by bv_omega
  have hzero : (BitVec.ofNat 32 snd - 1 = 0) ↔ snd = 1 := by bv_omega
  refine_uir []
  all_goals refine_lifted [not_true_eq_false, hdec, hzero, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [hdec, hzero, even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_even_true_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .even true fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hs : snd = 1 := by simpa using atom8
  subst snd
  refine_uir []
  all_goals refine_lifted [not_true_eq_false,  even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [ even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_swap_false_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .swap false fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hdec : (BitVec.ofNat 32 snd - 1).setWidth 64 =
      (BitVec.ofNat 32 (snd - 1)).setWidth 64 := by bv_omega
  have hzero : (BitVec.ofNat 32 snd - 1 = 0) ↔ snd = 1 := by bv_omega
  refine_uir []
  all_goals refine_lifted [not_true_eq_false, hdec, hzero, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [hdec, hzero, even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_swap_true_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .swap true fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hs : snd = 1 := by simpa using atom9
  subst snd
  refine_uir []
  all_goals refine_lifted [not_true_eq_false,  even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [ even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_add_false_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .add false fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hdec : (BitVec.ofNat 32 snd - 1).setWidth 64 =
      (BitVec.ofNat 32 (snd - 1)).setWidth 64 := by bv_omega
  have hzero : (BitVec.ofNat 32 snd - 1 = 0) ↔ snd = 1 := by bv_omega
  refine_uir []
  all_goals refine_lifted [not_true_eq_false, hdec, hzero, even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [hdec, hzero, even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

set_option maxHeartbeats 600000 in
theorem shift_add_true_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout .add true fr controls).BlockSimulation code .shift := by
  refine_intro
  simp only [next, swap, numerator, even, positive, Bool.beq_eq_decide_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  have hs : snd = 1 := by simpa using atom9
  subst snd
  refine_uir []
  all_goals refine_lifted [not_true_eq_false,  even, positive, swap, numerator, next]
  all_goals try contradiction
  all_goals try refine_close [ even, positive, swap, numerator, next]
  all_goals try simp_all [even, positive, swap, numerator, next]
  all_goals try bv_omega
  all_goals try (split <;> rfl)

theorem shift_block (path : Path) (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout path last fr controls).BlockSimulation code .shift := by
  cases path <;> cases last
  · exact shift_even_false_block code fr controls
  · exact shift_even_true_block code fr controls
  · exact shift_swap_false_block code fr controls
  · exact shift_swap_true_block code fr controls
  · exact shift_add_false_block code fr controls
  · exact shift_add_true_block code fr controls

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch
