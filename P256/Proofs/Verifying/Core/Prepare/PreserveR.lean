import P256.Proofs.Verifying.Core.Prepare.SecondCheck.Correct
import P256.Proofs.Verifying.Core.Prepare.CopyS.Correct
import P256.Proofs.Verifying.Core.Prepare.Nonzero
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem nonzero_r [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {r : Nat}
    (pre : Core.Pre s boundary) (agrees : AgreesExcept (nonzeroClobbers s) t u)
    (value : Nat256At t (stackPtr s-472#64) r) :
    Nat256At u (stackPtr s-472#64) r := by
  refine ⟨value.1,fun i hi => (agrees.byte ?_).trans (value.2 i hi)⟩
  intro c hc cover
  simp only [nonzeroClobbers,compareClobbers,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hc
  rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j,hj,eq⟩ := cover
  · exact stack_sub_apart pre.stack (a := 1184) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi eq.symm
  · exact stack_sub_apart pre.stack (a := 1192) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi eq.symm
  · exact stack_sub_apart pre.stack (a := 1200) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi eq.symm
  · exact stack_sub_apart pre.stack (a := 1185) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi eq.symm
  · have address : frameBase s+128#64 = stackPtr s-1048#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    change stackPtr s-472#64+BitVec.ofNat 64 i =
      frameBase s+128#64+BitVec.ofNat 64 j at eq
    rw [address] at eq
    exact stack_sub_apart pre.stack (a := 1048) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi eq.symm

theorem second_check_r [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (effect : (SecondCheck.Block.effect t).Holds t u)
    (value : Nat256At t (stackPtr s-472#64) r) :
    Nat256At u (stackPtr s-472#64) r := by
  refine ⟨value.1,fun i hi => (effect.agrees.byte ?_).trans (value.2 i hi)⟩
  intro c hc cover
  simp only [SecondCheck.Block.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j,hj,eq⟩ := cover
  all_goals change stackPtr s-472#64+BitVec.ofNat 64 i =
    stackPtr t+_+BitVec.ofNat 64 j at eq
  all_goals rw [state.rsp] at eq
  · apply stack_sub_apart pre.stack (a := 1176) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+0 = stackPtr s-1176#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1168) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+8 = stackPtr s-1168#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1160) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+16 = stackPtr s-1160#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1152) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+24 = stackPtr s-1152#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1048) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+128 = stackPtr s-1048#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1040) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+136 = stackPtr s-1040#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1032) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+144 = stackPtr s-1032#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 1024) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+152 = stackPtr s-1024#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm


theorem copy_s_r [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (effect : (CopyS.Block.effect t).Holds t u)
    (value : Nat256At t (stackPtr s-472#64) r) :
    Nat256At u (stackPtr s-472#64) r := by
  refine ⟨value.1,fun i hi => (effect.agrees.byte ?_).trans (value.2 i hi)⟩
  intro c hc cover
  simp only [CopyS.Block.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j,hj,eq⟩ := cover
  all_goals change stackPtr s-472#64+BitVec.ofNat 64 i =
    stackPtr t+_+BitVec.ofNat 64 j at eq
  all_goals rw [state.rsp] at eq
  · apply stack_sub_apart pre.stack (a := 440) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+736 = stackPtr s-440#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 432) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+744 = stackPtr s-432#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 424) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+752 = stackPtr s-424#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm
  · apply stack_sub_apart pre.stack (a := 416) (b := 472) (by decide) (by decide)
      (by decide) (by decide) (by decide) j hj i hi
    have address : stackPtr s-1176+760 = stackPtr s-416#64 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at eq
    exact eq.symm

end P256.Proofs.Verifying.Core.Prepare
