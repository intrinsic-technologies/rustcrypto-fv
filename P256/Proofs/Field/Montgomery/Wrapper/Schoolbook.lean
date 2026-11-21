import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Field.Schoolbook

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem schoolbook_work_frame (pre : CalleePre s boundary entryPC 32 32 280)
    (rsp : stackPtr t = stackPtr s - 144)
    (destination : t.regValue .rdi = stackPtr s - 72)
    (result : CalleeResult t u boundary 64 136) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 32, workRegion s] := by
  have hb := stack_bounds pre.stack
  have hspn : (stackPtr t).toNat = (stackPtr s).toNat - 144 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have houtn : (t.regValue .rdi).toNat = (stackPtr s).toNat - 72 := by
    rw [destination]
    exact stack_sub_toNat pre.stack (by decide)
  intro a hout
  apply result.frame a
  intro r hr hin
  apply hout (workRegion s) (by simp)
  have hr' : r = registerRegion t .rdi 64 ∨ r = Stack.region t 136 := by simpa using hr
  change (stackPtr s).toNat - 280 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 280 + 272
  rcases hr' with rfl | rfl
  · change (t.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rdi).toNat + 64 at hin
    rw [houtn] at hin
    constructor <;> omega
  · change (stackPtr t).toNat - 136 ≤ a.toNat ∧
      a.toNat < (Stack.region t 136).start + (Stack.region t 136).size at hin
    rw [stack_region_end] at hin
    change (stackPtr t).toNat - 136 ≤ a.toNat ∧ a.toNat < (stackPtr t).toNat + 8 at hin
    rw [hspn] at hin
    constructor <;> omega

theorem input_of_frame {a : Nat} (pre : CalleePre s boundary entryPC 32 32 280)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 280])
    (ha : Nat256At s (s.regValue .rsi) a) : Nat256At t (s.regValue .rsi) a := by
  refine ⟨ha.1, fun i hi => Eq.trans (frame _ ?_) (ha.2 i hi)⟩
  intro region hr hin
  have hinput := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion s .rdi 32 ∨ region = Stack.region s 280 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hinput hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hinput hin

theorem right_of_frame {b : Nat} (pre : MultiplyPre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 280])
    (hb : Nat256At s (s.regValue .rdx) b) : Nat256At t (s.regValue .rdx) b := by
  refine ⟨hb.1, fun i hi => Eq.trans (frame _ ?_) (hb.2 i hi)⟩
  intro region hr hin
  have hright := memoryRegion_contains_add pre.rightBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion s .rdi 32 ∨ region = Stack.region s 280 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.rightOutput _ hright hin
  · exact pre.rightStack _ hright hin

theorem entered_state {rightReg : Syntax.Reg} {ret : BitVec 64}
    (pre : CalleePre s boundary entryPC 32 32 280)
    (entry : SchoolbookEntry s t boundary rightReg ret) :
    SavedState s t := by
  refine {
    bindingsSupported := entry.pre.bindingsSupported
    machine := entry.pre.machine
    loaded := entry.pre.loaded
    allocated := entry.agrees.grow
    frame := ?_
    registers := ?_
    directionFlag := entry.pre.directionFlag
    mxcsr := entry.agrees.mxcsr (by simp [entryComponents])
    fp87 := entry.agrees.fcw (by simp [entryComponents])
    savedRbx := ?_
    returnWord := ?_ }
  · apply entry.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [entryComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨Stack.region s 280, by simp,
      ScalarFrame.stack_contains pre (by decide) (by decide) ha⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact entry.agrees.read (n := 64) (r := 5) (by simp [entryComponents])
      | exact entry.agrees.read (n := 64) (r := 12) (by simp [entryComponents])
      | exact entry.agrees.read (n := 64) (r := 13) (by simp [entryComponents])
      | exact entry.agrees.read (n := 64) (r := 14) (by simp [entryComponents])
      | exact entry.agrees.read (n := 64) (r := 15) (by simp [entryComponents])
  · rw [entry.memory]
    simp only [BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · rw [entry.memory]
    conv => lhs; arg 2; rw [← BitVec.add_zero (stackPtr s)]
    simp only [BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rw [BitVec.add_zero]
    rfl

theorem schoolbook_of_entry {a b : Nat} {rightReg : Syntax.Reg} {ret : BitVec 64}
    (pre : CalleePre s boundary entryPC 32 32 280)
    (entry : SchoolbookEntry s t boundary rightReg ret)
    (left : Nat256At t (t.regValue .rsi) a) (right : Nat256At t (t.regValue .rcx) b) :
    ∃ fuel u, Advances boundary fuel s u ∧ FrameState s u ∧ u.RIP = ret ∧
      Bytes u.external (scratch s + 64) 64 (fun i => UInt8.ofNat ((a*b) / 256^i % 256)) := by
  have state := entered_state pre entry
  obtain ⟨final, result, output⟩ := Schoolbook.schoolbook_correct entry.pre left right
  have saved := state.after_result pre result
    (schoolbook_work_frame pre entry.rsp entry.destination result)
  have sp : stackPtr final = scratch s := by
    change final.regValue .rsp = scratch s
    rw [result.rsp]
    change stackPtr t + 8 = stackPtr s - 136
    rw [entry.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have bx : final.regValue .rbx = s.regValue .rdi :=
    (result.calleeSaved .rbx (by simp)).trans entry.output
  obtain ⟨n, run⟩ := entry.execution
  obtain ⟨m, calleeRun⟩ := result.execution
  refine ⟨n+m, final, run.trans calleeRun, ⟨saved, sp, bx⟩,
    result.rip.trans entry.returnAddress, ?_⟩
  have dst : t.regValue .rdi = scratch s + 64 := by
    rw [entry.destination]
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd]
  rwa [dst] at output

theorem schoolbook_stage {a b : Nat} (pre : MultiplyPre s boundary)
    (ha : Nat256At s (s.regValue .rsi) a) (hb : Nat256At s (s.regValue .rdx) b) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t ∧ t.RIP = 0x1138b3 ∧
      Bytes t.external (scratch s + 64) 64 (fun i => UInt8.ofNat ((a*b) / 256^i % 256)) := by
  obtain ⟨entered, entry⟩ := schoolbook_entry_correct pre
  have state := entered_state pre.toCalleePre entry
  have left : Nat256At entered (entered.regValue .rsi) a := by
    rw [entry.left]
    exact input_of_frame pre.toCalleePre state.frame ha
  have right : Nat256At entered (entered.regValue .rcx) b := by
    rw [entry.right]
    exact right_of_frame pre state.frame hb
  exact schoolbook_of_entry pre.toCalleePre entry left right

end P256.Proofs.Field.Montgomery.Wrapper
