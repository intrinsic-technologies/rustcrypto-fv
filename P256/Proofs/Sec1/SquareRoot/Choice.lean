import P256.Proofs.Sec1.SquareRoot.State
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem choice_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t) (rip : t.RIP = 0x11454d) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u ∧ u.RIP = 0x114552 ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      (∀ {offset len : Nat}, offset ≤ 584 → len ≤ offset + 8 → ∀ i < len,
        u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨u, run, ready, rsp, ripU, rax, agrees⟩ :=
    ScalarFrame.choice_step pre (frameOffset := 584) (by decide) (by decide)
      (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
      0x1454d 0x4b1e (by decide) (by decide +kernel) (by decide +kernel) rip
  have frame : MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s] := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    · exact ⟨workRegion s, by simp,
        ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩
    · exact ⟨workRegion s, by simp,
        ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩
  have saved := state.toSavedState.after_agrees pre ready agrees frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [ScalarFrame.choiceClobbers])
  refine ⟨u, run, ⟨saved, rsp.trans state.rsp⟩, ripU, rax, ?_⟩
  intro offset len ho hl i hi
  apply agrees.byte
  intro c hc hcovers
  simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcovers.elim
  all_goals
    obtain ⟨j, hj, he⟩ := hcovers
    have low := stack_bounds pre.stack
    have off := stack_sub_toNat pre.stack (offset := offset) (by omega)
    have sum : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat - offset + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
        off, Nat.mod_eq_of_lt (by omega)]
    have equality := congrArg BitVec.toNat he
    rw [sum, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : j < 2^64),
      stack_sub_toNat pre.stack (by decide), Nat.mod_eq_of_lt (by omega)] at equality
    omega

end P256.Proofs.Sec1.SquareRoot
