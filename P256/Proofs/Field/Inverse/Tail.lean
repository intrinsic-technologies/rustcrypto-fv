import P256.Proofs.Field.Inverse.Tail.FirstCopyResult
import P256.Proofs.Field.Inverse.Tail.SecondCopyResult
import P256.Proofs.Field.Inverse.Tail.ChoiceEntry
import P256.Proofs.Field.Inverse.Tail.FirstPrepare
import P256.Proofs.Field.Inverse.Tail.SecondPrepare
import P256.Proofs.Field.Inverse.Tail.OutputResult
import P256.Proofs.Field.Inverse.Return

set_option autoImplicit false


open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem inverse_tail_value [Bindings] {s t : RamState} {boundary : ReturnBoundary} {beta n : Nat} {select : Bool}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11411e) (input : Nat256At t (stackPtr s - 168) beta)
    (flag : t.external[stackPtr s - 136]? = some (if select then 1 else 0)) (run : Advances boundary n s t) :
    ∃ u, CalleeResult s u boundary 40 880 ∧ Nat256At u (s.regValue .rdi) (if select then beta else 0) ∧
      u.external[s.regValue .rdi + 32]? = some (if select then 1 else 0) := by
  obtain ⟨n1,t1,run1,state1,rip1,candidate1,agrees1⟩ := FirstCopy.copy_stage pre state rip input
  have flag1 : t1.external[stackPtr s - 136]? = some (if select then 1 else 0) := by
    have h := copy_byte (destination := 112) (offset := 32) (by decide) (by decide)
      (.inl (by decide)) agrees1
    have addr : stackPtr t + 32#64 = stackPtr s - 136 := state.stack_address 32
    rw [addr] at h
    exact h.trans flag
  obtain ⟨t2,run2,state2,rip2,di2,mem2⟩ := choice_prepare_flag (select := select) pre state1 rip1 flag1
  have candidate2 : Nat256At t2 (stackPtr s - 56) beta :=
    nat256At_copy candidate1 (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
  obtain ⟨t3,run3,state3,rip3,ax3,bytes3⟩ := choice_stage pre state2 rip2
  have ax3' : t3.regValue .rax = (if select then 1 else 0) := by
    change t3.regValue .rax = ((t2.regValue .rdi).setWidth 8).setWidth 64 at ax3
    rw [di2] at ax3
    cases select <;> exact ax3
  have candidate3 : Nat256At t3 (stackPtr s - 56) beta :=
    nat256At_copy candidate2 (bytes3 (by decide) (by decide))
  obtain ⟨n4,t4,run4,state4,rip4,candidate4⟩ := first_prepare_selected (select := select) pre state3 rip3 ax3' candidate3
  obtain ⟨n5,t5,run5,state5,rip5,bp5,candidate5⟩ :=
    select_stage pre state4 (by decide) false rip4 candidate4
  obtain ⟨n6,t6,run6,state6,rip6,candidate6,agrees6⟩ :=
    SecondCopy.copy_stage pre state5 rip5 candidate5
  have bp6 : t6.regValue .rbp = (if select then 1 else 0) :=
    (agrees6.read (r := 5) (n := 64) (by simp [copyComponents])).trans bp5
  obtain ⟨n7,t7,run7,state7,rip7,candidate7⟩ := second_prepare_selected (select := select) pre state6 rip6 bp6 candidate6
  obtain ⟨n8,t8,run8,state8,rip8,bp8,candidate8⟩ :=
    select_stage pre state7 (by decide) true rip7 candidate7
  have candidate8' : Nat256At t8 (stackPtr s - 168) (if select then beta else 0) := by
    cases select <;> exact candidate8
  obtain ⟨n9,t9,run9,state9,rip9,output9,flag9⟩ :=
    output_stage (select := select) pre state8 rip8 bp8 candidate8'
  obtain ⟨u,result,mem⟩ := finish_return pre state9 rip9
    (((((((((run.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9)
  refine ⟨u,result,nat256At_copy output9 (fun i hi => congrArg (fun m : Ram => m[_]?) mem),?_⟩
  rw [mem]
  exact flag9

theorem inverse_tail_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {value n : Nat} {select : Bool} (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11411e)
    (flag : t.external[stackPtr s - 136]? = some (if select then 1 else 0))
    (candidate : select = true → Nat256At t (stackPtr s - 168) value)
    (run : Advances boundary n s t) :
    ∃ u, CalleeResult s u boundary 40 880 ∧
      Nat256At u (s.regValue .rdi) (if select then value else 0) ∧
      u.external[s.regValue .rdi + 32]? = some (if select then 1 else 0) := by
  have raw := nat256At_readLimbs (s := t) (address := stackPtr s - 168)
    (fun i hi => state.allocated _
      ((stack_sub_readable pre.stack (offset := 168) (len := 32)
        (by decide) (by decide)).mem i hi))
  obtain ⟨u, result, output, flagOut⟩ := inverse_tail_value pre state rip raw flag run
  refine ⟨u, result, ?_, flagOut⟩
  cases hselect : select with
  | false => simpa only [hselect, Bool.false_eq_true, ↓reduceIte] using output
  | true =>
    have eqValue := readLimbs_toNat (candidate hselect)
    simpa only [hselect, ↓reduceIte, eqValue] using output

end P256.Proofs.Field.Inverse
