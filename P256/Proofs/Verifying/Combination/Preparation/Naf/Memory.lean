import P256.Proofs.Verifying.Combination.StackRegion
import P256.Proofs.Verifying.Combination.Naf.Serialize.Interface
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Verifying.Combination.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines

def scalarCallLayout : StackCallLayout 8808 8 272 536 :=
  ⟨6560, 6528, 6240, by decide, by decide, by decide, by decide, by decide, by decide, .inl (by decide)⟩

theorem scalar_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {po : Nat}
    (pre : Pre s boundary) (state : State s t 6560)
    (pointLow : 6368 ≤ po) (pointHigh : po ≤ 6496)
    (rip : t.RIP = 0x10b170) (input : t.regValue .rsi = stackPtr s - 6528)
    (output : t.regValue .rdi = stackPtr s - 6240)
    (cursor : memLoad t.external (stackPtr s - 6528) 64 = stackPtr s - 6520)
    (point : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - BitVec.ofNat 64 po)
    (ret : InProgram (returnBoundary t).rip) :
    Combination.Naf.Serialize.ScalarPre t boundary (stackPtr s - 6520) (stackPtr s - BitVec.ofNat 64 po) := by
  have cp := CalleePre.of_stack pre scalarCallLayout state.bindingsSupported state.machine state.directionFlag state.loaded
    state.allocated rip state.rsp input output ret
  refine ⟨cp, ?_, point, localRegion_bounded pre (offset := 6520) (by decide) (by decide),
    localRegion_allocated pre state (offset := 6520) (by decide) (by decide),
    localRegion_avoids pre (offset := 6520) (by decide) (by decide), ?_,
    localRegion_bounded pre (by omega) (by omega),
    localRegion_allocated pre state (by omega) (by omega), ?_, ?_⟩
  · rw [input]
    exact cursor
  · intro region hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (localRegion s 6520 8).Disjoint ⟨(t.regValue .rsi).toNat, 8⟩
      rw [input]
      exact localRegion_disjoint pre (a := 6520) (b := 6528) (by decide) (by decide) (.inl (by decide))
    · exact localRegion_disjoint pre (a := 6520) (b := po) (by decide) (by omega) (.inr (by omega))
    · change (localRegion s 6520 8).Disjoint ⟨(t.regValue .rdi).toNat, 272⟩
      rw [output]
      exact localRegion_disjoint pre (a := 6520) (b := 6240) (by decide) (by decide) (.inr (by decide))
    · exact localRegion_stack_disjoint pre state (offset := 6520) (by decide)
  · change (localRegion s po 128).Disjoint ⟨(t.regValue .rdi).toNat, 272⟩
    rw [output]
    exact localRegion_disjoint pre (a := po) (b := 6240) (by omega) (by decide) (.inr (by omega))
  · exact localRegion_stack_disjoint pre state (by omega)


open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scalar_result_work [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Combination.Naf.Serialize.ScalarResult entry t boundary (stackPtr s - 6520) point)
    (output : entry.regValue .rdi = stackPtr s - 6240) :
    MemoryWriteFrame entry t #v[workRegion s 8808] := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr entry).toNat = (stackPtr s).toNat - 6560 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 6560) (by decide)
  have hout : (entry.regValue .rdi).toNat = (stackPtr s).toNat - 6240 := by
    rw [output]
    exact stack_sub_toNat pre.stack (offset := 6240) (by decide)
  have hcursor : (stackPtr s - 6520).toNat = (stackPtr s).toNat - 6520 :=
    stack_sub_toNat pre.stack (offset := 6520) (by decide)
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (workRegion s 8808) (by simp)
  have hr' : region = registerRegion entry .rdi 272 ∨
      region = Combination.Naf.Serialize.cursorRegion (stackPtr s - 6520) ∨ region = Stack.region entry 536 := by simpa using hr
  change (stackPtr s).toNat - 8808 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 8808 + 8760
  rcases hr' with rfl | rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (entry.regValue .rdi).toNat + 272 at hin
    rw [hout] at hin
    constructor <;> omega
  · change (stackPtr s - 6520).toNat ≤ a.toNat ∧ a.toNat < (stackPtr s - 6520).toNat + 8 at hin
    rw [hcursor] at hin
    constructor <;> omega
  · change (stackPtr entry).toNat - 536 ≤ a.toNat ∧
      a.toNat < (Stack.region entry 536).start + (Stack.region entry 536).size at hin
    rw [stack_region_end, hsp] at hin
    constructor <;> omega

theorem after_scalar [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Combination.Naf.Serialize.ScalarResult entry t boundary (stackPtr s - 6520) point)
    (output : entry.regValue .rdi = stackPtr s - 6240) : State s t := by
  have work := scalar_result_work pre state result output
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

theorem scalar_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary} {point : BitVec 64}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : Combination.Naf.Serialize.ScalarResult entry t boundary (stackPtr s - 6520) point)
    (output : entry.regValue .rdi = stackPtr s - 6240) {offset len : Nat}
    (ho : offset ≤ 6552) (hl : len ≤ offset + 8)
    (apartOutput : offset + 272 ≤ 6240 ∨ 6240 + len ≤ offset)
    (apartCursor : offset + 8 ≤ 6520 ∨ 6520 + len ≤ offset)
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
  have hr' : region = registerRegion entry .rdi 272 ∨
      region = Combination.Naf.Serialize.cursorRegion (stackPtr s - 6520) ∨ region = Stack.region entry 536 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat < (entry.regValue .rdi).toNat + 272 at hin
    rw [output, show (stackPtr s - 6240).toNat = (stackPtr s).toNat - 6240 from
      stack_sub_toNat pre.stack (offset := 6240) (by decide), ha] at hin
    omega
  · change (stackPtr s - 6520).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat < (stackPtr s - 6520).toNat + 8 at hin
    rw [show (stackPtr s - 6520).toNat = (stackPtr s).toNat - 6520 from
      stack_sub_toNat pre.stack (offset := 6520) (by decide), ha] at hin
    omega
  · change (stackPtr entry).toNat - 536 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region entry 536).start + (Stack.region entry 536).size at hin
    rw [stack_region_end, state.rsp, show (stackPtr s - 6560).toNat = (stackPtr s).toNat - 6560 from
      stack_sub_toNat pre.stack (offset := 6560) (by decide), ha] at hin
    omega


end P256.Proofs.Verifying.Combination.Preparation.Naf
