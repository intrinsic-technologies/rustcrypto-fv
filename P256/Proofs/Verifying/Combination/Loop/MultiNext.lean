import P256.Proofs.Verifying.Combination.Loop.MultiAdvance
import P256.Proofs.Verifying.Combination.Loop.MultiCounterStep
import P256.Proofs.Verifying.Combination.Loop.MultiCounterBranch
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem next_left [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point true 0x10f2b8) :
    ∃ fuel w, Advances boundary fuel t w ∧ DigitState s w tables digits p q u v k point false := by
  obtain ⟨fuel, w, run, stateW, ripW, cursorW, tableW, remainingW, frame⟩ :=
    advance_digit true pre state.toFrameState state.rip state.remaining
  refine ⟨fuel, w, run, ⟨⟨state.toRoundData.after_registers
    (readyToStep stateW.machine stateW.bindingsSupported) frame (by simp [Component.Covers])
    (by simp), ?_, ?_, remainingW, ?_⟩, ripW, ?_⟩⟩
  · have cursor : t.regValue .r13 = digits + BitVec.ofNat 64 (k+7) := by
      have h := state.cursor
      change t.regValue .r13 = digits + 0#64 + BitVec.ofNat 64 (k+7) at h
      simpa only [BitVec.add_zero] using h
    rw [cursor] at cursorW
    change w.regValue .r13 = digits + 272#64 + BitVec.ofNat 64 (k+7)
    apply cursorW.trans
    change digits + BitVec.ofNat 64 (k+7) + 272#64 = digits + 272#64 + BitVec.ofNat 64 (k+7)
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (k+7)) (272#64), ← BitVec.add_assoc]
  · have table : t.regValue .rbp = tables := by
      have h := state.tableCursor
      change t.regValue .rbp = tables + 0#64 at h
      simpa only [BitVec.add_zero] using h
    rw [table] at tableW
    exact tableW
  · rw [frame.external (by simp [Component.Covers])]
    exact state.savedCursor
  · intro h
    have eq : w.regValue .r14 = t.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
    exact state.identity (by rwa [eq] at h)

theorem next_right [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v (k+1) point false 0x10f2b8)
    (bound : k < 257) :
    ∃ fuel w, Advances boundary fuel t w ∧
      ((k = 0 ∧ Memory s w tables digits p q u v ∧ w.RIP = 0x10f301 ∧
          ProjectiveAt w (stackPtr s - 336) point ∧
          memLoad w.external (stackPtr s - 392) 64 = s.regValue .rdi) ∨
       RoundState s w tables digits p q u v k point) := by
  obtain ⟨fa, a, runA, stateA, ripA, _, _, _, frameA⟩ :=
    advance_digit false pre state.toFrameState state.rip state.remaining
  obtain ⟨b, runB, stateB, ripB, countB, cursorB, frameB⟩ :=
    counter_step pre stateA ripA
      ((frameA.read (n := 64) (r := 3) (by simp)).trans state.count)
      (by
        rw [frameA.external (by simp [Component.Covers])]
        simpa only [Nat.add_assoc] using state.savedCursor)
  obtain ⟨w, runW, stateW, ripW, frameW⟩ := countdown_branch pre stateB ripB countB (by omega)
  have frame : AgreesExcept [.reg 13, .reg 5, .reg 12, .reg 3, .flags, .rip] t w :=
    ((frameA.trans frameB).trans frameW).mono (by simp)
  have memory := state.toMemory.after_registers
    (readyToStep stateW.machine stateW.bindingsSupported) frame (by simp [Component.Covers]) (by simp)
  have valueW : ProjectiveAt w (stackPtr s - 336) point :=
    state.value.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?)
      (frame.external (by simp [Component.Covers])))
  have outputW : memLoad w.external (stackPtr s - 392) 64 = s.regValue .rdi := by
    rw [frame.external (by simp [Component.Covers])]; exact state.output
  refine ⟨fa+3+2, w, (runA.trans runB).trans runW, ?_⟩
  by_cases zero : k = 0
  · exact Or.inl ⟨zero, memory, by simpa only [ite_eq_left zero] using ripW, valueW, outputW⟩
  refine Or.inr ⟨⟨memory,
    (frameW.read (n := 64) (r := 3) (by simp)).trans countB,
    Nat.pos_of_ne_zero zero, by have h := state.bounded; omega,
    (frame.read (n := 64) (r := 15) (by simp)).trans state.scratch, valueW, ?_, ?_, outputW⟩,
    by simpa only [ite_eq_right zero] using ripW,
    (frameW.read (n := 64) (r := 13) (by simp)).trans cursorB, ?_⟩
  · rw [frame.external (by simp [Component.Covers])]; exact state.total
  · rw [frame.external (by simp [Component.Covers])]; exact state.tableBase
  · intro h
    have eq : w.regValue .r14 = t.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
    exact state.identity (by rwa [eq] at h)

end P256.Proofs.Verifying.Combination.Loop.Multi
