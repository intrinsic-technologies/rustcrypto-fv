import P256.Proofs.Verifying.Combination.Loop.MultiDigitState
import P256.Proofs.Verifying.Combination.Loop.MultiSaveCursor
import P256.Proofs.Verifying.Combination.PointMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem save_inner_cursor [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : RoundState s t tables digits p q u v k point 0x10f1ad)
    (remaining : t.regValue .r12 = 2) (tableCursor : t.regValue .rbp = tables) :
    ∃ w, Advances boundary 1 t w ∧ DigitState s w tables digits p q u v k point true 0x10f1b2 := by
  obtain ⟨w, run, stateW, ripW, cursorW, frame⟩ := save_digit_cursor pre state.toFrameState state.rip
  have read_kept (offset : Nat) (bound : offset ≤ 1432) (size : 8 ≤ offset + 8)
      (apart : offset + 8 ≤ 376 ∨ 376 + 8 ≤ offset) :
      memLoad w.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_agrees_apart frame
    intro address size h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq, reduceCtorEq, or_false] at h
    obtain ⟨rfl,rfl⟩ := h
    exact stack_sub_apart pre.stack (by decide) bound (by decide) size apart
  have valueW : ProjectiveAt w (stackPtr s - 336) point := by
    apply state.value.of_bytes_eq
    intro i hi
    apply frame.byte
    intro component hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j,hj,eq⟩ := covered
      exact stack_sub_apart pre.stack (a := 376) (b := 336) (by decide) (by decide)
        (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
    · exact covered.elim
  refine ⟨w, run, ⟨⟨⟨state.toMemory.of_frame pre stateW,
    (frame.read (n := 64) (r := 3) (by simp)).trans state.count,
    state.positive, state.bounded,
    (frame.read (n := 64) (r := 15) (by simp)).trans state.scratch,
    valueW, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ripW, ?_⟩⟩
  · exact (read_kept 400 (by decide) (by decide) (.inr (by decide))).trans state.total
  · exact (read_kept 384 (by decide) (by decide) (.inr (by decide))).trans state.tableBase
  · exact (read_kept 392 (by decide) (by decide) (.inr (by decide))).trans state.output
  · change w.regValue .r13 = digits + 0#64 + BitVec.ofNat 64 (k+7)
    rw [BitVec.add_zero]
    exact (frame.read (n := 64) (r := 13) (by simp)).trans state.cursor
  · change w.regValue .rbp = tables + 0#64
    rw [BitVec.add_zero]
    exact (frame.read (n := 64) (r := 5) (by simp)).trans tableCursor
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans remaining
  · exact cursorW.trans state.cursor
  · intro h
    have eq : w.regValue .r14 = t.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
    exact state.identity (by rwa [eq] at h)

end P256.Proofs.Verifying.Combination.Loop.Multi
