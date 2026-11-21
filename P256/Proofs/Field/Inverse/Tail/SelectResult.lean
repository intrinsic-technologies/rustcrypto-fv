import P256.Proofs.Field.Inverse.Tail.SelectCall
import P256.Proofs.Program.LimbSelect

set_option autoImplicit false

open P256.Proofs.Program.LimbSelect (limb_select32_correct)
open P256.Proofs.Program (CalleePre CalleeResult stack_region_end)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem select_result_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (rsp : stackPtr t = stackPtr s - 176) (dst : t.regValue .rdi = stackPtr s - 168)
    (result : CalleeResult t u boundary 32 80) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s] := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat - 176 := by
    rw [rsp]; exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hdi : (t.regValue .rdi).toNat = (stackPtr s).toNat - 168 := by
    rw [dst]; exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  intro a hout
  apply result.frame a
  intro r hr hin
  apply hout (workRegion s) (by simp)
  have hr' : r = registerRegion t .rdi 32 ∨ r = Stack.region t 80 := by simpa using hr
  change (stackPtr s).toNat - 880 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 880 + 864
  rcases hr' with rfl | rfl
  · change (t.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rdi).toNat + 32 at hin
    rw [hdi] at hin
    constructor <;> omega
  · change (stackPtr t).toNat - 80 ≤ a.toNat ∧
      a.toNat < (Stack.region t 80).start + (Stack.region t 80).size at hin
    rw [stack_region_end, hsp] at hin
    constructor <;> omega

theorem select_result [Bindings] {s t t1 : RamState} {boundary : ReturnBoundary}
    {beta source : Nat} {select : Bool} {ret : BitVec 64}
    (pre : Pre s boundary) (state : SelectCallState s t source select)
    (hsource : 48 ≤ source ∧ source ≤ 136) (hret : InProgram ret)
    (ready1 : ReadyToStep t1)
    (effect1 : (callEffect (fun _ => 0x1191c0) ret t).Holds t t1)
    (candidate : Nat256At t (stackPtr s - BitVec.ofNat 64 (if select then source else 168)) beta) :
    ∃ n u, Advances boundary n t1 u ∧ FrameState s u ∧ u.RIP = ret ∧
      u.regValue .rbp = (if select then 1 else 0) ∧ Nat256At u (stackPtr s - 168) beta := by
  have calleePre := select_call_pre pre state hsource hret ready1 effect1
  have state1 := state.toFrameState.toSavedState.after_agrees pre ready1 effect1.agrees
    (select_call_frame pre state effect1) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  have sp1 : stackPtr t1=stackPtr s-176 := effect1.writes.1.trans (select_call_address state)
  have dst1 : t1.regValue .rdi=stackPtr s-168 :=
    (effect1.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have src1 : t1.regValue .rdx=stackPtr s-BitVec.ofNat 64 source :=
    (effect1.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
  have r81 : t1.regValue .r8=if select then 1 else 0 :=
    (effect1.agrees.read (r := 8) (n := 64) (by simp)).trans state.r8
  have rbp1 : t1.regValue .rbp=if select then 1 else 0 :=
    (effect1.agrees.read (r := 5) (n := 64) (by simp)).trans state.rbp
  have bytes {offset len : Nat} (ho : offset≤168) (hl : len≤offset+8) :
      ∀ i<len, t1.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    apply effect1.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨j,hj,he⟩ := hcov
    rw [select_call_address state] at he
    exact stack_sub_apart pre.stack (a := 176) (b := offset) (by decide) (by omega)
      (by decide) hl (.inl (by omega)) j hj i hi he.symm
  have candidate1 : Nat256At t1 (stackPtr s-BitVec.ofNat 64 (if select then source else 168)) beta :=
    nat256At_copy candidate (bytes (by cases select <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
      (by cases select <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega))
  obtain ⟨t2,result,selected⟩ := limb_select32_correct (select := select) calleePre r81
  obtain ⟨n2,run2⟩ := result.execution
  have state2 := state1.after_result pre result (select_result_frame pre sp1 dst1 result)
  refine ⟨n2,t2,run2,⟨state2,?_⟩,
    result.rip.trans (callEffect_stack effect1).1,(result.calleeSaved .rbp (by simp)).trans rbp1,?_⟩
  · change t2.regValue .rsp = _
    rw [result.rsp]
    change stackPtr t1+8 = _
    rw [sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  · apply nat256At_copy candidate1
    intro i hi
    have h := selected i hi
    cases select <;> simpa only [dst1, src1, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] using h

end P256.Proofs.Field.Inverse
