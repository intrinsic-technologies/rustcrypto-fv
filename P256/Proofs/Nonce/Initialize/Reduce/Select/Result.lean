import P256.Proofs.Nonce.Initialize.Reduce.Select.Pre
import X86Proofs.Instructions.Movs.RepTriple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.LimbSelect

variable [Bindings] {initial s t u : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original difference : Nat} {select : Bool}

theorem selection_word
    (pre : InitializePre initial boundary orderAddress)
    (state : SelectionReady initial s boundary original difference select)
    (effect : (callEffect (fun _ => 0x1191c0) 0x107b5c s).Holds s t)
    (result : CalleeResult t u boundary 32 80)
    {offset : Nat} (lower : 40 ≤ offset) (upper : offset + 8 ≤ 232) :
    memLoad u.external (stackPtr u + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
  have sp : stackPtr u = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr s).toNat = (stackPtr initial).toNat - 280 := by
    rw [state.stage.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have tn : (stackPtr t).toNat = (stackPtr initial).toNat - 288 := by
    have hsp : stackPtr t = stackPtr initial - 288 :=
      effect.writes.1.trans (ScalarFrame.scalar_call_address state.stage.toFrameState)
    rw [hsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : t.regValue .rdi = stackPtr s + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have dn : (t.regValue .rdi).toNat = (stackPtr initial).toNat - 280 + 8 := by
    rw [dst]
    change (stackPtr s + BitVec.ofNat 64 8).toNat = _
    rw [toNat_add_ofNat _ _ (by rw [sn]; omega), sn]
  rw [sp]
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  rw [result.frame _]
  · have addr : stackPtr s + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (280-offset) := by
      have hn : 280 = (280 - offset) + offset := by omega
      rw [state.stage.rsp, show (280 : BitVec 64) = BitVec.ofNat 64 280 by rfl,
        hn, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel, Nat.add_sub_cancel]
    rw [addr]
    exact ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState effect (offset := 280-offset) (len := 8)
      (by omega) (by omega) hi
  · intro region hr hin
    have an : (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - 280 + offset + i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        toNat_add_ofNat _ _ (by rw [sn]; omega), sn]
      omega
    have cases : region = registerRegion t .rdi 32 ∨ region = Stack.region t 80 := by
      simpa using hr
    rcases cases with rfl | rfl
    · change (t.regValue .rdi).toNat ≤ _ ∧ _ < (t.regValue .rdi).toNat + 32 at hin
      rw [dn, an] at hin
      omega
    · change (stackPtr t).toNat - 80 ≤ _ ∧ _ <
        (Stack.region t 80).start + (Stack.region t 80).size at hin
      rw [stack_region_end, tn, an] at hin
      omega

theorem selection_result
    (pre : InitializePre initial boundary orderAddress)
    (state : SelectionReady initial s boundary original difference select)
    (entryFrame : Stage initial t boundary 288)
    (effect : (callEffect (fun _ => 0x1191c0) 0x107b5c s).Holds s t)
    (result : CalleeResult t u boundary 32 80)
    (selected : SelectedBytesAt t u select) :
    Selected initial u boundary (if select then original else difference) := by
  have sp : stackPtr u = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  have dst : t.regValue .rdi = stackPtr s + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have src : t.regValue .rdx = stackPtr s + 104 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.source
  have di : t.regValue .rdi = stackPtr initial - 272 := by
    rw [dst, state.stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have memory := FieldCall.stack_result_work_frame (frameOffset := 280) pre.toCalleePre
    entryFrame.toFrameState result di (by decide) (by decide) (by decide) (by decide)
  have finalStage : Stage initial u boundary := by
    obtain ⟨n, hn⟩ := entryFrame.execution
    obtain ⟨m, hm⟩ := result.execution
    exact ⟨FieldCall.after_result pre.toCalleePre entryFrame.toFrameState result (by decide) memory,
      n + m, hn.trans hm⟩
  refine {
    stage := finalStage
    rip := result.rip.trans (callEffect_stack effect).1
    secret := (selection_word pre state effect result (offset := 184) (by decide) (by decide)).trans state.secret
    output := (selection_word pre state effect result (offset := 192) (by decide) (by decide)).trans state.output
    length := (selection_word pre state effect result (offset := 176) (by decide) (by decide)).trans state.length
    entropy := (selection_word pre state effect result (offset := 168) (by decide) (by decide)).trans state.entropy
    outputPointer := (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp [pushEffect_components])).trans state.outputPointer)
    buffer := ?_
    value := ?_
  }
  · rw [sp]
    exact (result.calleeSaved .rbp (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans state.buffer)
  · rw [sp]
    constructor
    · cases select
      · exact state.difference.1
      · exact state.original.1
    · intro i hi
      have daddr : stackPtr s + 8 = stackPtr initial - 272 := by
        rw [state.stage.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      have saddr : stackPtr s + 104 = stackPtr initial - 176 := by
        rw [state.stage.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      have h := selected i hi
      rw [dst, src] at h
      rw [h]
      cases select
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have v := state.difference.2 i hi
        rw [daddr] at v ⊢
        exact (ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState effect
          (offset := 272) (len := 32) (by decide) (by decide) hi).trans
          v
      · simp only [↓reduceIte]
        have v := state.original.2 i hi
        rw [saddr] at v ⊢
        exact (ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState effect
          (offset := 176) (len := 32) (by decide) (by decide) hi).trans
          v

end P256.Proofs.Nonce.Initialize.Reduce
