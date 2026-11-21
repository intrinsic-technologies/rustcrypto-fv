import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Stage
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Control

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem finish_round [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {n : Nat} (pre : Pre s boundary)
    (state : RoundState s t n 0x1033be 336 (ProjectiveLoop.accumulator table (digits s) (n+1)))
    (rax : t.regValue .rax = stackPtr s-144) :
    ∃ fuel u, Advances boundary fuel t u ∧ LoopState s u table (n+1) := by
  obtain ⟨v, runV, stateV, ripV, frameV⟩ :=
    skip_table_loop pre state.toFrameState state.rip state.rbx state.r14
  have memoryV : v.external = t.external := frameV.external (by simp [Component.Covers])
  have remainingV : (Operand.mem (stackPtr s-344) : Operand 64).read v =
      BitVec.ofNat 64 (63-n) := by
    change memLoad v.external _ 64 = _
    rw [memoryV]
    exact state.remaining
  obtain ⟨fuelU, u, runU, stateU, ripU, cursorU, remainingU, tableU, frameU⟩ :=
    end_iteration pre stateV ripV (show 63-n < 64 by omega) remainingV
  have frame : AgreesExcept [.reg 3, .reg 15, .reg 9, .flags, .rip] t u :=
    (frameV.trans frameU).mono (by simp)
  have memory : u.external = t.external := frame.external (by simp [Component.Covers])
  have cursorV : (Operand.mem (stackPtr s-368) : Operand 64).read v =
      s.regValue .rcx+BitVec.ofNat 64 (63-n) := by
    change memLoad v.external _ 64 = _
    rw [memoryV]
    exact state.cursor
  have nextCount : 64-(n+1) = 63-n := by omega
  refine ⟨4+fuelU, u, runV.trans runU, stateU, by have := state.bound; omega, ?_,
    state.value.of_bytes_eq (by intro i hi; rw [memory]; rfl),
    (frame.read (n := 64) (r := 13) (by simp)).trans state.r13,
    (frame.read (n := 64) (r := 14) (by simp)).trans state.r14, ?_, ?_, ?_,
    (frame.read (n := 64) (r := 0) (by simp)).trans rax, ?_, ?_, ?_⟩
  · rw [ripU]
    by_cases last : 63-n = 0
    · have hn : ¬ n+1 < 64 := by have := state.bound; omega
      simp only [last, ↓reduceIte, hn]
    · have hn : n+1 < 64 := by have := state.bound; omega
      simp only [last, ↓reduceIte, hn]
  · rw [nextCount]
    exact remainingU
  · rw [tableU]
    change memLoad v.external _ 64 = _
    rw [memoryV]
    exact state.table
  · rw [nextCount]
    exact cursorU.trans (congrArg (fun x : BitVec 64 => x-1) cursorV)
  all_goals change memLoad u.external _ 64 = _
  all_goals rw [memory]
  · exact state.count
  · exact state.output
  · exact state.table

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
