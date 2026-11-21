import K256.Proofs.Common.CFG.Simulation

namespace K256.Proofs.ParseSignature

open K256.Proofs.CFG

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {P : Program Op Label signature results} {D : Dialect Op Value Store}

theorem resume_arguments
    (frame : StackFrame Value Label (fun _ ↦ results) results)
    (output : Output Value Store results) :
    (frame.resume output).arguments = output.values := by
  rcases frame with @⟨size, target, kept, arity, guard⟩
  have hs : size = 0 := by change results + size = results at arity; omega
  subst size
  have hk : kept = #v[] := Vector.eq_empty
  subst kept
  rfl

theorem step_append_stack {s t : CFG.State Value Store Label signature results}
    (h : P.step D s = .next t) (tail : List (StackFrame Value Label signature results)) :
    P.step D ⟨s.location, s.stack ++ tail⟩ = .next ⟨t.location, t.stack ++ tail⟩ := by
  rcases s with ⟨loc, stack⟩
  cases hb : P.runBlock D loc with
  | jump target =>
    simp only [Program.step, hb, Transfer.next] at h ⊢
    cases h
    rfl
  | call target frame =>
    simp only [Program.step, hb, Transfer.next] at h ⊢
    cases h
    rfl
  | returned output =>
    cases stack with
    | nil =>
      simp only [Program.step, hb, Transfer.next] at h
      contradiction
    | cons frame rest =>
      simp only [Program.step, hb, Transfer.next] at h
      split at h
      next ha =>
        cases h
        simp only [Program.step, hb, List.cons_append, Transfer.next, ha, ↓reduceIte]
      next => contradiction
  | stuck =>
    simp only [Program.step, hb, Transfer.next] at h
    contradiction

theorem step_done_resume {s : CFG.State Value Store Label signature results}
    {output : Output Value Store results} (h : P.step D s = .done output)
    (frame : StackFrame Value Label signature results)
    (tail : List (StackFrame Value Label signature results))
    (ha : frame.Accepts D output.tag = true) :
    P.step D ⟨s.location, s.stack ++ frame :: tail⟩ =
      .next ⟨frame.resume output, tail⟩ := by
  rcases s with ⟨loc, stack⟩
  cases hb : P.runBlock D loc with
  | jump target =>
    simp only [Program.step, hb, Transfer.next] at h
    contradiction
  | call target inner =>
    simp only [Program.step, hb, Transfer.next] at h
    contradiction
  | returned result =>
    cases stack with
    | nil =>
      simp only [Program.step, hb, Transfer.next, Outcome.done.injEq] at h
      cases h
      simp only [Program.step, hb, List.nil_append, Transfer.next, ha, ↓reduceIte]
    | cons inner rest =>
      simp only [Program.step, hb, Transfer.next] at h
      split at h <;> contradiction
  | stuck =>
    simp only [Program.step, hb, Transfer.next] at h
    contradiction

theorem exec_reaches_resume {s : CFG.State Value Store Label signature results}
    {output : Output Value Store results} (h : P.Exec D s output)
    (frame : StackFrame Value Label signature results)
    (tail : List (StackFrame Value Label signature results))
    (ha : frame.Accepts D output.tag = true) :
    (P.sem D).Reaches ⟨s.location, s.stack ++ frame :: tail⟩
      ⟨frame.resume output, tail⟩ := by
  induction h with
  | done hd => exact .single (step_done_resume hd frame tail ha)
  | next hs _ ih => exact .step (step_append_stack hs _) (ih ha)

theorem exec_call {caller callee : Location Value Store Label signature}
    {frame : StackFrame Value Label signature results}
    {tail : List (StackFrame Value Label signature results)}
    {output final : Output Value Store results}
    (hcall : P.runBlock D caller = .call callee frame)
    (hcallee : P.Exec D ⟨callee, []⟩ output)
    (ha : frame.Accepts D output.tag = true)
    (hcontinue : P.Exec D ⟨frame.resume output, tail⟩ final) :
    P.Exec D ⟨caller, tail⟩ final := by
  apply Program.Exec.next (next := ⟨callee, frame :: tail⟩)
  · simp only [Program.step, hcall, Transfer.next]
  · apply Program.Exec.of_sem
    exact (exec_reaches_resume hcallee frame tail ha).exec hcontinue.sem

end K256.Proofs.ParseSignature
