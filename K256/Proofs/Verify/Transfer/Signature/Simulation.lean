import K256.Proofs.Common.CFG.Simulation

namespace K256.Proofs.Verify.Transfer.Signature

open K256.Proofs.CFG

variable {O : Nat → Type} {A B V M : Type} {r : Nat}
variable (p : Program O B (fun _ : B => r) r) (d : Dialect O V M)
variable (L : Location V M A (fun _ : A => r) → Location V M B (fun _ : B => r) → Prop)
variable (R : Output V M r → Output V M r → Prop)

private abbrev FrameMatches (f : StackFrame V A (fun _ : A => r) r)
    (g : StackFrame V B (fun _ : B => r) r) : Prop :=
  ∀ a b, R a b → f.Accepts d a.tag = true →
    g.Accepts d b.tag = true ∧ L (f.resume a) (g.resume b)

inductive Matches : Transfer V M A (fun _ : A => r) r → Transfer V M B (fun _ : B => r) r → Prop where
  | stuck {t} : Matches .stuck t
  | jump {x y} : L x y → Matches (.jump x) (.jump y)
  | call {x y f g} : L x y → FrameMatches d L R f g → Matches (.call x f) (.call y g)
  | ret {a b} : R a b → Matches (.returned a) (.returned b)
  | advance {s y} : Matches s (p.runBlock d y) → Matches s (.jump y)

private inductive StacksMatch :
    List (StackFrame V A (fun _ : A => r) r) → List (StackFrame V B (fun _ : B => r) r) → Prop where
  | nil : StacksMatch [] []
  | cons {f g fs gs} :
    FrameMatches d L R f g → StacksMatch fs gs → StacksMatch (f :: fs) (g :: gs)

private def StatesMatch (s : State V M A (fun _ : A => r) r)
    (t : State V M B (fun _ : B => r) r) : Prop :=
  L s.location t.location ∧ StacksMatch d L R s.stack t.stack

variable {p d L R}

private theorem Matches.outcome {s t} (matched : Matches p d L R s t)
    {fs gs} (stacks : StacksMatch d L R fs gs)
    {y} (runTarget : p.runBlock d y = t) :
    (s.next d fs).MatchedBy (p.sem d) (StatesMatch d L R) R ⟨y, gs⟩ := by
  induction matched generalizing y with
  | stuck => trivial
  | @jump _ z loc =>
    refine ⟨⟨z, gs⟩, .single ?_, loc, stacks⟩
    simp only [Program.sem, Program.step, runTarget, Transfer.next_jump]
  | @call _ z _ g loc frame =>
    refine ⟨⟨z, g :: gs⟩, .single ?_, loc, .cons frame stacks⟩
    simp only [Program.sem, Program.step, runTarget, Transfer.next_call]
  | ret out =>
    cases stacks with
    | nil =>
      refine ⟨_, .ret ?_, out⟩
      simp only [Program.sem, Program.step, runTarget, Transfer.next_returned_nil]
    | @cons f g fs gs frame tail =>
      rename_i a b
      by_cases accepts : f.Accepts d a.tag = true
      · obtain ⟨accepts', loc⟩ := frame _ _ out accepts
        simp only [Transfer.next, accepts, ite_true]
        refine ⟨⟨g.resume b, gs⟩, .single ?_, loc, tail⟩
        simp only [Program.sem, Program.step, runTarget, Transfer.next, accepts', ite_true]
      · simp only [Transfer.next, accepts, Bool.false_eq_true, ite_false, Outcome.MatchedBy]
  | @advance s z _ ih =>
    have step : (p.sem d).Step ⟨y, gs⟩ ⟨z, gs⟩ := by
      simp only [Program.sem, Program.step, runTarget, Transfer.next_jump]
    have rest := ih rfl
    cases eq : s.next d fs with
    | stuck => trivial
    | next =>
      rw [eq] at rest
      obtain ⟨t, reaches, related⟩ := rest
      exact ⟨t, .step step reaches, related⟩
    | done =>
      rw [eq] at rest
      obtain ⟨b, run, related⟩ := rest
      exact ⟨b, .step step run, related⟩

variable (p d L R)

theorem exec_of_matches (q : Program O A (fun _ : A => r) r)
    (blocks : ∀ x y, L x y → Matches p d L R (q.runBlock d x) (p.runBlock d y))
    {x y a} (run : q.Exec d ⟨x, []⟩ a) (related : L x y) :
    ∃ b, p.Exec d ⟨y, []⟩ b ∧ R a b := by
  have sim : Simulation (p.sem d) (q.sem d) (StatesMatch d L R) R := by
    apply Simulation.of_blocks
    rintro label arguments store fs ⟨y, gs⟩ ⟨loc, stacks⟩
    exact (blocks _ _ loc).outcome stacks rfl
  obtain ⟨b, execution, out⟩ := sim.exec run.sem (a := ⟨y, []⟩) ⟨related, .nil⟩
  exact ⟨b, Program.Exec.of_sem execution, out⟩

end K256.Proofs.Verify.Transfer.Signature
