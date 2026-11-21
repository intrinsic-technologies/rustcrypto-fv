import P256.Proofs.Verifying.Combination.Table.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Code
import X86Proofs.Program.ReadWrite.RepString

set_option autoImplicit false

open P256.Proofs.Program (stack_region_end supportedMachine_of_ready_agrees)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def workRegion (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 2120, 2088⟩

theorem stack_address {s t : RamState} (hsp : stackPtr t = stackPtr s - 1096)
    {offset : Nat} (h : offset ≤ 1096) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (1096-offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 1096 offset (by omega) h, hsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : TablePre s boundary cursor point) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ 2120) (hl : len + 32 ≤ offset)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have low := P256.Proofs.Program.stack_sub_toNat pre.stack ho
  rw [toNat_add_ofNat _ _ (by rw [low]; omega), low]
  change (stackPtr s).toNat - 2120 ≤ _ ∧ _ < (stackPtr s).toNat - 2120 + 2088
  constructor <;> omega

theorem output_work_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : TablePre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 768, workRegion s]) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120] := by
  intro a ha
  apply memory a
  intro region hr hin
  have hr' : region = registerRegion s .rdi 768 ∨ region = workRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) hin
  · apply ha (Stack.region s 2120) (by simp)
    have bounds := P256.Proofs.Program.stack_bounds pre.stack
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2120 + 2088 at hin
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧
      a.toNat < (Stack.region s 2120).start + (Stack.region s 2120).size
    rw [stack_region_end]
    constructor <;> omega

theorem output_work_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : TablePre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 768, workRegion s])
    {offset n : Nat} (ho : offset ≤ 32) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have low := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have hr' : region = registerRegion s .rdi 768 ∨ region = workRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    change (stackPtr s).toNat - 2120 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region s 2120).start + (Stack.region s 2120).size
    rw [stack_region_end, toNat_add_ofNat _ _ (by rw [low]; omega), low]
    constructor <;> omega
  · change (stackPtr s).toNat - 2120 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (stackPtr s).toNat - 2120 + 2088 at hin
    rw [toNat_add_ofNat _ _ (by rw [low]; omega), low] at hin
    omega

theorem loaded_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (frame : MemoryWriteFrame s t
      #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120]) :
    ProgramLoaded t := by
  intro a b hb
  rw [frame a]
  · exact pre.loaded a b hb
  · intro region hr ha
    have hr' : region = registerRegion s .rdi 768 ∨ region = cursorRegion cursor ∨
        region = Stack.region s 2120 := by simpa using hr
    rcases hr' with rfl | rfl | rfl
    · exact pre.avoids _ (by simp) a ha (.inl ⟨b, hb⟩)
    · exact pre.cursorAvoids a ha (.inl ⟨b, hb⟩)
    · exact pre.avoids _ (by simp) a ha (.inl ⟨b, hb⟩)

theorem after [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64} {cs : List Component}
    (pre : TablePre s boundary cursor point) (state : FrameState s t cursor)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 768, workRegion s])
    (sp : .reg 4 ∉ cs) (bp : .reg 5 ∉ cs) (r13 : .reg 13 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s u cursor := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (output_work_frame pre memory)
  refine ⟨P256.Proofs.Program.bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    loaded_of_frame pre total, agrees.directionFlagClear (by component_not_mem) state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), total,
    (agrees.read (n := 64) (r := 4) sp).trans state.rsp, ?_,
    (agrees.read (n := 64) (r := 5) bp).trans state.rbp,
    (agrees.read (n := 64) (r := 13) r13).trans state.r13, ?_,
    (agrees.mxcsr (by component_not_mem)).trans state.mxcsr,
    (agrees.fcw (by component_not_mem)).trans state.fp87⟩
  · intro entry he
    have bound : entry.2 ≤ 32 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre memory bound (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    {offset len codeOffset codeLen : Nat}
    (hoff : offset ≤ 2120) (hlen : len ≤ offset + 8)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 2120) (by simp) _
    (P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre
      (offset := offset) (len := len) hoff hlen ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

end P256.Proofs.Verifying.Combination.Table
