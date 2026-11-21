import P256.Proofs.Verifying.Combination.Naf.Machine.State
import X86Proofs.Program.ReadWrite.RepString

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def workRegion (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 168, 120⟩

theorem stack_address {s t : RamState} (hsp : stackPtr t = stackPtr s - 136)
    {offset : Nat} (h : offset ≤ 136) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (136-offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 136 offset (by omega) h, hsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ 168) (hl : len + 48 ≤ offset)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have low := P256.Proofs.Program.stack_sub_toNat pre.stack ho
  rw [toNat_add_ofNat _ _ (by rw [low]; omega), low]
  change (stackPtr s).toNat - 168 ≤ _ ∧ _ < (stackPtr s).toNat - 168 + 120
  constructor <;> omega

theorem output_work_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 257, workRegion s]) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 257, Stack.region s 168] := by
  intro a ha
  apply memory a
  intro region hr hin
  have hr' : region = registerRegion s .rdi 257 ∨ region = workRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) hin
  · apply ha (Stack.region s 168) (by simp)
    have bounds := P256.Proofs.Program.stack_bounds pre.stack
    change (stackPtr s).toNat - 168 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 168 + 120 at hin
    change (stackPtr s).toNat - 168 ≤ a.toNat ∧
      a.toNat < (Stack.region s 168).start + (Stack.region s 168).size
    rw [stack_region_end]
    constructor <;> omega

theorem output_work_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 257, workRegion s])
    {offset n : Nat} (ho : offset ≤ 48) (hl : n/8 ≤ offset+8) :
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
  have hr' : region = registerRegion s .rdi 257 ∨ region = workRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    change (stackPtr s).toNat - 168 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region s 168).start + (Stack.region s 168).size
    rw [stack_region_end, toNat_add_ofNat _ _ (by rw [low]; omega), low]
    constructor <;> omega
  · change (stackPtr s).toNat - 168 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (stackPtr s).toNat - 168 + 120 at hin
    rw [toNat_add_ofNat _ _ (by rw [low]; omega), low] at hin
    omega

theorem after [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cs : List Component}
    {stackOffset : BitVec 64}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t stackOffset)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 257, workRegion s])
    (sp : .reg 4 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s u stackOffset := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (output_work_frame pre memory)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    P256.Proofs.Program.ScalarFrame.loaded_of_frame pre total, agrees.directionFlagClear hdf state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), total,
    (agrees.read (n := 64) (r := 4) sp).trans state.rsp, ?_, ?_,
    (agrees.mxcsr hmxcsr).trans state.mxcsr,
    (agrees.fcw hfcw).trans state.fp87⟩
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre memory bound (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t)
    {offset len : Nat} (bound : offset + len ≤ 136) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  rw [stack_address state.rsp (by omega)]
  exact P256.Proofs.Program.readable_of_grow
    (P256.Proofs.Program.stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t)
    {offset len : Nat} (bound : offset + len ≤ 136) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  have readable := stack_readable pre state bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi hreserved
  apply pre.avoids (Stack.region s 168) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  rw [stack_address state.rsp (by omega)]
  exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 136)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [stack_address state.rsp (by omega)]
  exact stack_code_apart pre (by omega) (by omega) codeBound

end P256.Proofs.Verifying.Combination.Naf.Machine
