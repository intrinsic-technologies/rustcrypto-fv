import P256.Proofs.Verifying.Combination.TablePre
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem table_result_work [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Table.TableResult entry t boundary (stackPtr s - 6496) point)
    (output : entry.regValue .rdi = stackPtr s - 4656) :
    MemoryWriteFrame entry t #v[workRegion s 8808] := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr entry).toNat = (stackPtr s).toNat - 6560 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 6560) (by decide)
  have hout : (entry.regValue .rdi).toNat = (stackPtr s).toNat - 4656 := by
    rw [output]
    exact stack_sub_toNat pre.stack (offset := 4656) (by decide)
  have hcursor : (stackPtr s - 6496).toNat = (stackPtr s).toNat - 6496 :=
    stack_sub_toNat pre.stack (offset := 6496) (by decide)
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (workRegion s 8808) (by simp)
  have hr' : region = registerRegion entry .rdi 768 ∨
      region = Table.cursorRegion (stackPtr s - 6496) ∨ region = Stack.region entry 2120 := by simpa using hr
  change (stackPtr s).toNat - 8808 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 8808 + 8760
  rcases hr' with rfl | rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (entry.regValue .rdi).toNat + 768 at hin
    rw [hout] at hin
    constructor <;> omega
  · change (stackPtr s - 6496).toNat ≤ a.toNat ∧ a.toNat < (stackPtr s - 6496).toNat + 8 at hin
    rw [hcursor] at hin
    constructor <;> omega
  · change (stackPtr entry).toNat - 2120 ≤ a.toNat ∧
      a.toNat < (Stack.region entry 2120).start + (Stack.region entry 2120).size at hin
    rw [stack_region_end, hsp] at hin
    constructor <;> omega

theorem after_table [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Table.TableResult entry t boundary (stackPtr s - 6496) point)
    (output : entry.regValue .rdi = stackPtr s - 4656) : State s t := by
  have work := table_result_work pre state result output
  have hw : MemoryWriteFrame entry t #v[registerRegion s .rdi 96, workRegion s 8808] := by
    intro a ha
    apply work a
    intro r hr
    exact ha r (by simpa using Or.inr hr)
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre hw), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre (by decide) hw hb (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre (by decide) hw (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem table_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Table.TableResult entry t boundary (stackPtr s - 6496) point)
    (output : entry.regValue .rdi = stackPtr s - 4656) {offset len : Nat}
    (ho : offset ≤ 6552) (hl : len ≤ offset + 8)
    (apartOutput : offset + 768 ≤ 4656 ∨ 4656 + len ≤ offset)
    (apartCursor : offset + 8 ≤ 6496 ∨ 6496 + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have ha : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    have low := stack_sub_toNat pre.stack (offset := offset) (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [low]; omega), low]
  apply result.frame
  intro region hr hin
  have hr' : region = registerRegion entry .rdi 768 ∨
      region = Table.cursorRegion (stackPtr s - 6496) ∨ region = Stack.region entry 2120 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat < (entry.regValue .rdi).toNat + 768 at hin
    rw [output, show (stackPtr s - 4656).toNat = (stackPtr s).toNat - 4656 from
      stack_sub_toNat pre.stack (offset := 4656) (by decide), ha] at hin
    omega
  · change (stackPtr s - 6496).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat < (stackPtr s - 6496).toNat + 8 at hin
    rw [show (stackPtr s - 6496).toNat = (stackPtr s).toNat - 6496 from
      stack_sub_toNat pre.stack (offset := 6496) (by decide), ha] at hin
    omega
  · change (stackPtr entry).toNat - 2120 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region entry 2120).start + (Stack.region entry 2120).size at hin
    rw [stack_region_end, state.rsp, show (stackPtr s - 6560).toNat = (stackPtr s).toNat - 6560 from
      stack_sub_toNat pre.stack (offset := 6560) (by decide), ha] at hin
    omega


end P256.Proofs.Verifying.Combination
