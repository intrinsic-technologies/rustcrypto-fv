import K256.Proofs.Ecdh.Transfer.Generate
import K256.Proofs.Ecdh.Transfer.Operands
import K256.Proofs.Common.Lift.Lockstep
import K256.Spec.Program.Extracted.Image

namespace K256.Proofs.Ecdh.Transfer

open X86.Machine X86.UserProcess X86Proofs K256.Spec.Program CFG Lift

private abbrev code := Extracted.programImage
private noncomputable abbrev d := dialect code
private abbrev MachineState := State Value Ram LIR.Label signature Reg.count
private abbrev MachineOutcome := Outcome Value Ram LIR.Label signature Reg.count

private def nop : Op 0 :=
  .exec 0x11f77b (fun s => s.RIP = 0x11f77b) (fun _ => nopEffect 0x11f77b 5) (Reg.operands [] [])

private def nextArgs : Vector (Fin 54) 53 :=
  RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11),
    (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54

private theorem nextArgs_ofFn : Vector.ofFn (fun i : Fin 53 => nextArgs[i]) = nextArgs := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem mergedBlock :
    merged.blocks .l11f77b =
      .letOp nop #v[] (mapOperands (fun i : Fin 53 => nextArgs[i]) LIR.b_l11f780) := by
  with_unfolding_all rfl

private noncomputable def stepTwice (s : MachineState) : MachineOutcome :=
  match LIR.program.step d s with
  | .next state => LIR.program.step d state
  | .done out => .done out
  | .stuck => .stuck

private theorem nopBlock :
    LIR.program.blocks .l11f77b =
      .letOp nop #v[] (.terminate (.br ⟨.l11f780, nextArgs⟩)) := rfl

private theorem evalNop (tail : Block Op LIR.Label signature Reg.count 54)
    (a : Values Value Reg.count) (m : Ram) :
    (Block.letOp nop #v[] tail).eval d a m =
      match d.eval nop (a.select #v[]) m with
      | some (x, n) => tail.eval d (a.push x) n
      | none => .stuck := by
  cases h : d.eval nop (a.select #v[]) m with
  | none => simp only [Block.eval, h]
  | some result =>
    obtain ⟨value, next⟩ := result
    simp only [Block.eval, h]

private theorem splitStep (a : Values Value Reg.count) (m : Ram)
    (stk : List (StackFrame Value LIR.Label signature Reg.count)) :
    merged.step d ⟨⟨.l11f77b, a, m⟩, stk⟩ = stepTwice ⟨⟨.l11f77b, a, m⟩, stk⟩ := by
  unfold stepTwice
  simp only [Program.step, Program.runBlock, mergedBlock, nopBlock, evalNop]
  cases h : d.eval nop (a.select #v[]) m with
  | none => rfl
  | some result =>
    obtain ⟨value, next⟩ := result
    simp only [eval_mapOperands, nextArgs_ofFn, Block.eval, Terminator.eval, Edge.eval,
      Transfer.next_jump]
    rfl

private theorem mergedBlock_other {l : LIR.Label} (h : l ≠ .l11f77b) :
    merged.blocks l = LIR.program.blocks l := by
  cases l <;> first | rfl | (rename_i x; cases x <;> first | rfl | contradiction)

private def Follows (s : MachineState) (r : MachineOutcome) : Prop :=
  match r with
  | .done out => LIR.program.Exec d s out
  | .next next => ∀ {out}, LIR.program.Exec d next out → LIR.program.Exec d s out
  | .stuck => True

private theorem follows_step (s : MachineState) : Follows s (LIR.program.step d s) := by
  cases h : LIR.program.step d s with
  | done => exact .done h
  | next => exact .next h
  | stuck => trivial

private theorem follows_twice (s : MachineState) : Follows s (stepTwice s) := by
  unfold stepTwice
  split
  · rename_i n h
    have tail := follows_step n
    cases eq : LIR.program.step d n with
    | done =>
      rw [eq] at tail
      exact .next h tail
    | next =>
      rw [eq] at tail
      exact fun {_} run => .next h (tail run)
    | stuck => trivial
  · exact .done ‹_›
  · trivial

private theorem follows_merged (s : MachineState) : Follows s (merged.step d s) := by
  by_cases hx : s.location.label = .l11f77b
  · rcases s with ⟨⟨l, a, m⟩, stk⟩
    change l = .l11f77b at hx
    subst l
    rw [splitStep]
    exact follows_twice _
  · simp only [Program.step, Program.runBlock, mergedBlock_other hx]
    exact follows_step _

theorem mergedExec {s : MachineState} {o : Output Value Ram Reg.count}
    (run : merged.Exec d s o) : LIR.program.Exec d s o := by
  induction run with
  | @done state _ h =>
    have step := follows_merged state
    rw [h] at step
    exact step
  | @next state _ _ h _ ih =>
    have step := follows_merged state
    rw [h] at step
    exact step ih

end K256.Proofs.Ecdh.Transfer
