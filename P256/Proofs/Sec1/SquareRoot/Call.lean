import P256.Proofs.Sec1.SquareRoot.State
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem call_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (offset : Nat) (disp : BitVec 32) (size : offset + 5 ≤ 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64))) (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 1 t u ∧ SavedState s u ∧
      stackPtr u = stackPtr s - 592 ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) t).Holds t u := by
  obtain ⟨u, run, ready, effect⟩ := ScalarFrame.call_step pre (frameOffset := 584)
    (by decide) (by decide) (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp offset disp size bytes (inProgram_low target) target rip
  have push : pushAddr t = stackPtr s - 592 := by
    rw [pushAddr, state.rsp, BitVec.sub_sub]
    rfl
  have frame : MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact ha.elim
    rw [push] at ha
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩
  refine ⟨u, run, state.toSavedState.after_agrees pre ready effect.agrees frame ?_,
    effect.writes.1.trans push, effect⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [pushEffect_components]

theorem stack_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve outputOffset : Nat} (pre : Pre s boundary)
    (state : SavedState s entry) (rsp : stackPtr entry = stackPtr s - 592)
    (output : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (capacity : 592 + reserve ≤ 2176) (outputBound : outputOffset ≤ 2176)
    (outputBelow : outputBytes + 40 ≤ outputOffset)
    (result : CalleeResult entry t boundary outputBytes reserve) : FrameState s t := by
  have work := result.stack_frame pre.stack rsp output capacity (by decide) outputBound outputBelow
  refine ⟨state.after_result pre result ?_, ?_⟩
  · intro a ha
    apply work a
    intro r hr
    have eq : r = workRegion s := by simpa using hr
    subst r
    exact ha _ (by simp)
  · have hr : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hr]
    rw [rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl

theorem stack_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve outputOffset offset len : Nat} (pre : Pre s boundary)
    (rsp : stackPtr entry = stackPtr s - 592)
    (output : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hout : outputOffset ≤ 2176) (ho : offset ≤ 584) (hlen : len ≤ offset + 8)
    (apart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have off := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 592 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [output]
    exact stack_sub_toNat pre.stack hout
  have addr : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [off]; omega), off]
  apply result.frame
  intro r hr hin
  have cases : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  rcases cases with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (entry.regValue .rdi).toNat + outputBytes at hin
    rw [dst, addr] at hin
    omega
  · change (stackPtr entry).toNat - reserve ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end, sp, addr] at hin
    omega

end P256.Proofs.Sec1.SquareRoot
