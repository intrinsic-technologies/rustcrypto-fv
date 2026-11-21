import P256.Proofs.Verifying.Combination.Table.Frame

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice stack_region_end readyToStep)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_result_work_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputOffset outputBytes reserve : Nat}
    (pre : TablePre s boundary cursor point) (state : FrameState s entry cursor 1104)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 2120) (hsaved : outputBytes + 32 ≤ outputOffset)
    (hreserve : reserve + 1104 ≤ 2120) :
    MemoryWriteFrame entry t #v[workRegion s] := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - 1104 := by
    rw [state.rsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 1104) (by decide)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack hout
  intro a ha
  apply result.frame a
  intro r hr hin
  apply ha (workRegion s) (by simp)
  have hr' : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2120 + 2088
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
    (pre : TablePre s boundary cursor point)
    (h : MemoryWriteFrame u t #v[workRegion s]) :
    MemoryWriteFrame u t #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120] := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  intro a ha
  apply h a
  intro region hr hin
  have he : region = workRegion s := by simpa using hr
  subst region
  apply ha (Stack.region s 2120) (by simp)
  change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2120 + 2088 at hin
  change (stackPtr s).toNat - 2120 ≤ a.toNat ∧
    a.toNat < (Stack.region s 2120).start + (Stack.region s 2120).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_read [Bindings] {s u t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : TablePre s boundary cursor point)
    (h : MemoryWriteFrame u t #v[workRegion s]) {offset n : Nat}
    (ho : offset ≤ 32) (hn : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hs := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [h _]
  intro r hr hin
  have he : r = workRegion s := by simpa using hr
  subst r
  change (stackPtr s).toNat - 2120 ≤ _ ∧
    (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (stackPtr s).toNat - 2120 + 2088 at hin
  rw [toNat_add_ofNat _ _ (by rw [hs]; omega), hs] at hin
  omega

theorem FrameState.after_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputBytes reserve : Nat}
    (pre : TablePre s boundary cursor point) (state : FrameState s entry cursor 1104)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hf : MemoryWriteFrame entry t #v[workRegion s]) : FrameState s t cursor := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (work_frame pre hf), ?_, ?_,
    (result.calleeSaved .rbp (by simp)).trans state.rbp,
    (result.calleeSaved .r13 (by simp)).trans state.r13, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 32 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    exact (work_read pre hf hb (by omega)).trans (state.saved entry he)
  · have h := work_read pre hf (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem FrameState.after_stack_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputOffset outputBytes reserve : Nat}
    (pre : TablePre s boundary cursor point) (state : FrameState s entry cursor 1104)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 2120) (hsaved : outputBytes + 32 ≤ outputOffset)
    (hreserve : reserve + 1104 ≤ 2120) : FrameState s t cursor :=
  state.after_result pre result
    (stack_result_work_frame pre state result destination hout hsaved hreserve)

theorem stack_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {outputOffset outputBytes reserve offset len : Nat}
    (pre : TablePre s boundary cursor point) (state : FrameState s entry cursor 1104)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 2120) (ho : offset ≤ 1096) (hlen : len ≤ offset + 8)
    (hapart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hs := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := offset) (by omega)
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - 1104 := by
    rw [state.rsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 1104) (by decide)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack hout
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

end P256.Proofs.Verifying.Combination.Table
