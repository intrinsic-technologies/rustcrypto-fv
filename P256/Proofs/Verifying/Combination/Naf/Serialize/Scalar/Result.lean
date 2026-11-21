import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Call
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Memory
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Call.Triple
import P256.Proofs.Program.Copy
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.Interface
import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.Program.Memory

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult StackCallLayout boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice stack_region_end readyToStep)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs


theorem stack_result_work_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputOffset outputBytes reserve : Nat}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s entry cursor 368)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 536) (hsaved : outputBytes + 16 ≤ outputOffset)
    (hreserve : reserve + 368 ≤ 536) :
    MemoryWriteFrame entry t #v[workRegion s] := by
  have hb := stack_bounds pre.stack
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - 368 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 368) (by decide)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact stack_sub_toNat pre.stack hout
  intro a ha
  apply result.frame a
  intro r hr hin
  apply ha (workRegion s) (by simp)
  have hr' : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  change (stackPtr s).toNat - 536 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 536 + 520
  rcases hr' with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (entry.regValue .rdi).toNat + outputBytes at hin
    rw [hdn] at hin
    constructor <;> omega
  · change (stackPtr entry).toNat - reserve ≤ a.toNat ∧
      a.toNat < (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end] at hin
    change (stackPtr entry).toNat - reserve ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8 at hin
    rw [hsn] at hin
    constructor <;> omega

theorem work_frame [Bindings] {s u t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : ScalarPre s boundary cursor point)
    (h : MemoryWriteFrame u t #v[workRegion s]) :
    MemoryWriteFrame u t #v[registerRegion s .rdi 272, cursorRegion cursor, Stack.region s 536] := by
  have hb := stack_bounds pre.stack
  intro a ha
  apply h a
  intro region hr hin
  have he : region = workRegion s := by simpa using hr
  subst region
  apply ha (Stack.region s 536) (by simp)
  change (stackPtr s).toNat - 536 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 536 + 520 at hin
  change (stackPtr s).toNat - 536 ≤ a.toNat ∧
    a.toNat < (Stack.region s 536).start + (Stack.region s 536).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_read [Bindings] {s u t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : ScalarPre s boundary cursor point)
    (h : MemoryWriteFrame u t #v[workRegion s]) {offset n : Nat}
    (ho : offset ≤ 16) (hn : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u := by
  have hb := stack_bounds pre.stack
  have hs := stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [h _]
  intro r hr hin
  have he : r = workRegion s := by simpa using hr
  subst r
  change (stackPtr s).toNat - 536 ≤ _ ∧
    (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (stackPtr s).toNat - 536 + 520 at hin
  rw [toNat_add_ofNat _ _ (by rw [hs]; omega), hs] at hin
  omega

theorem FrameState.after_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputBytes reserve : Nat}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s entry cursor 368)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hf : MemoryWriteFrame entry t #v[workRegion s]) : FrameState s t cursor := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (work_frame pre hf), ?_, ?_,
    (result.calleeSaved .rbp (by simp)).trans state.rbp,
    (result.calleeSaved .r12 (by simp)).trans state.r12,
    (result.calleeSaved .r13 (by simp)).trans state.r13,
    (result.calleeSaved .r15 (by simp)).trans state.r15, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 16 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    exact (work_read pre hf hb (by omega)).trans (state.saved entry he)
  · have h := work_read pre hf (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputOffset outputBytes reserve offset len : Nat}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s entry cursor 368)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 536) (ho : offset ≤ 360) (hlen : len ≤ offset + 8)
    (hapart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hb := stack_bounds pre.stack
  have hs := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - 368 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 368) (by decide)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact stack_sub_toNat pre.stack hout
  have ha : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [toNat_add_ofNat _ _ (by rw [hs]; omega), hs]
  apply result.frame
  intro r hr hin
  have hr' : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  rcases hr' with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (entry.regValue .rdi).toNat + outputBytes at hin
    rw [hdn, ha] at hin
    omega
  · change (stackPtr entry).toNat - reserve ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end, hsn, ha] at hin
    omega

theorem work_cursor_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[workRegion s]) :
    memLoad u.external cursor 64 = memLoad t.external cursor 64 := by
  apply cursor_read_of_frame pre
  intro a ha
  apply memory a
  intro region hr hin
  have hr' : region = workRegion s := by simpa using hr
  subst region
  apply ha (Stack.region s 536) (by simp)
  have bounds := stack_bounds pre.stack
  change (stackPtr s).toNat - 536 ≤ a.toNat ∧
    a.toNat < (stackPtr s).toNat - 536 + 520 at hin
  change (stackPtr s).toNat - 536 ≤ a.toNat ∧
    a.toNat < (Stack.region s 536).start + (Stack.region s 536).size
  rw [stack_region_end]
  constructor <;> omega

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
