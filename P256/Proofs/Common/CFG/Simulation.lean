import P256.Proofs.Common.CFG.Lemma.IR
import P256.Proofs.Common.Core.Simulation

namespace P256.Proofs.CFG

section Programs

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {program : Program Op Label signature results} {dialect : Dialect Op Value Store}
  {state : CFG.State Value Store Label signature results}
  {output left right : Output Value Store results}

def Program.sem (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) : Semantics where
  State := CFG.State Value Store Label signature results
  Output := Output Value Store results
  Step state next := program.step dialect state = .next next
  Ret state output := program.step dialect state = .done output

theorem Program.Exec.sem (h : program.Exec dialect state output) :
    (program.sem dialect).Exec state output := by
  induction h with
  | done h => exact .ret h
  | next h _ ih => exact .step h ih

theorem Program.Exec.of_sem {state : (program.sem dialect).State}
    {output : (program.sem dialect).Output} (h : (program.sem dialect).Exec state output) :
    program.Exec dialect state output := by
  induction h with
  | ret h => exact .done h
  | step h _ ih => exact .next h ih

theorem Program.exec_iff_sem :
    program.Exec dialect state output ↔ (program.sem dialect).Exec state output :=
  ⟨Program.Exec.sem, Program.Exec.of_sem⟩

theorem Program.exec_iff_run :
    program.Exec dialect state output ↔ ∃ fuel, program.run dialect fuel state = some output := by
  constructor
  · intro h
    induction h with
    | done h => exact ⟨1, by simp [Program.run, h]⟩
    | next h _ ih =>
        obtain ⟨fuel, hfuel⟩ := ih
        exact ⟨fuel + 1, by simp [Program.run, h, hfuel]⟩
  · rintro ⟨fuel, h⟩
    induction fuel generalizing state with
    | zero => simp [Program.run] at h
    | succ fuel ih =>
        cases hs : program.step dialect state with
        | done o =>
            simp only [Program.run, hs, Option.some.injEq] at h
            exact .done (h ▸ hs)
        | next next => exact .next hs (ih (by simpa [Program.run, hs] using h))
        | stuck => simp [Program.run, hs] at h

theorem Program.Exec.deterministic (hl : program.Exec dialect state left)
    (hr : program.Exec dialect state right) : left = right := by
  obtain ⟨m, hm⟩ := Program.exec_iff_run.mp hl
  obtain ⟨n, hn⟩ := Program.exec_iff_run.mp hr
  exact Program.run_deterministic hm hn

end Programs

section Blocks

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}

def Outcome.MatchedBy (lo : Semantics)
    (R : CFG.State Value Store Label signature results → lo.State → Prop)
    (post : Output Value Store results → lo.Output → Prop) (a : lo.State) :
    Outcome Value Store Label signature results → Prop
  | .next state => ∃ b, lo.Reaches a b ∧ R state b
  | .done output => ∃ o, lo.Exec a o ∧ post output o
  | .stuck => True

def Program.BlockSimulation (lo : Semantics) (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store)
    (R : CFG.State Value Store Label signature results → lo.State → Prop)
    (post : Output Value Store results → lo.Output → Prop) (label : Label) : Prop :=
  ∀ (arguments : Values Value (signature label)) (store : Store)
    (stack : List (StackFrame Value Label signature results)) (a : lo.State),
    R ⟨⟨label, arguments, store⟩, stack⟩ a →
      (program.step dialect ⟨⟨label, arguments, store⟩, stack⟩).MatchedBy lo R post a

variable {lo : Semantics} {program : Program Op Label signature results}
  {dialect : Dialect Op Value Store}
  {R : CFG.State Value Store Label signature results → lo.State → Prop}
  {post : Output Value Store results → lo.Output → Prop}

namespace Outcome

theorem MatchedBy.next {a b : lo.State} {state : CFG.State Value Store Label signature results}
    (h : lo.Reaches a b) (hR : R state b) : (Outcome.next state).MatchedBy lo R post a :=
  ⟨b, h, hR⟩

theorem MatchedBy.done {a : lo.State} {o : lo.Output} {output : Output Value Store results}
    (h : lo.Exec a o) (hpost : post output o) :
    (Outcome.done output : Outcome Value Store Label signature results).MatchedBy lo R post a :=
  ⟨o, h, hpost⟩

theorem MatchedBy.reaches {a b : lo.State} {t : Outcome Value Store Label signature results}
    (h : lo.Reaches a b) (hm : t.MatchedBy lo R post b) : t.MatchedBy lo R post a := by
  cases t with
  | next state =>
    obtain ⟨c, hbc, hc⟩ := hm
    exact ⟨c, h.trans hbc, hc⟩
  | done output =>
    obtain ⟨o, he, hp⟩ := hm
    exact ⟨o, h.exec he, hp⟩
  | stuck => trivial

theorem MatchedBy.mono {R' : CFG.State Value Store Label signature results → lo.State → Prop}
    {post' : Output Value Store results → lo.Output → Prop} {a : lo.State}
    {t : Outcome Value Store Label signature results} (hm : t.MatchedBy lo R post a)
    (hR : ∀ x b, R x b → R' x b) (hpost : ∀ o o', post o o' → post' o o') :
    t.MatchedBy lo R' post' a := by
  cases t with
  | next state =>
    obtain ⟨c, hac, hc⟩ := hm
    exact ⟨c, hac, hR _ _ hc⟩
  | done output =>
    obtain ⟨o, he, hp⟩ := hm
    exact ⟨o, he, hpost _ _ hp⟩
  | stuck => trivial

end Outcome

end Blocks

end P256.Proofs.CFG

namespace P256.Proofs.Simulation

open CFG

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {lo : Semantics} {program : Program Op Label signature results}
  {dialect : Dialect Op Value Store}
  {R : CFG.State Value Store Label signature results → lo.State → Prop}
  {post : Output Value Store results → lo.Output → Prop}

theorem of_blocks (h : ∀ label, program.BlockSimulation lo dialect R post label) :
    Simulation lo (program.sem dialect) R post where
  step := by
    rintro ⟨⟨label, arguments, store⟩, stack⟩ next a ha hs
    have hm := h label arguments store stack a ha
    change program.step dialect ⟨⟨label, arguments, store⟩, stack⟩ = .next next at hs
    rw [hs] at hm
    exact hm
  ret := by
    rintro ⟨⟨label, arguments, store⟩, stack⟩ output a ha hr
    have hm := h label arguments store stack a ha
    change program.step dialect ⟨⟨label, arguments, store⟩, stack⟩ = .done output at hr
    rw [hr] at hm
    exact hm

theorem block (sim : Simulation lo (program.sem dialect) R post) (label : Label) :
    program.BlockSimulation lo dialect R post label := by
  intro arguments store stack a ha
  cases hs : program.step dialect ⟨⟨label, arguments, store⟩, stack⟩ with
  | next state => exact sim.step (y := state) ha hs
  | done output => exact sim.ret (o := output) ha hs
  | stuck => trivial

end P256.Proofs.Simulation

namespace P256.Proofs.CFG

def Summary (L : Semantics) {α β : Type} (Entry : α → L.State → Prop) (f : α → β)
    (Done : β → L.State → Prop) : Prop :=
  ∀ a s, Entry a s → ∃ t, L.Reaches s t ∧ Done (f a) t

namespace Summary

variable {L : Semantics} {α β : Type} {Entry : α → L.State → Prop} {f : α → β}
  {Done : β → L.State → Prop}

theorem of_simulation {callee : Semantics} (entry : α → callee.State)
    (result : α → callee.Output) (hexec : ∀ a, callee.Exec (entry a) (result a))
    (hsim : ∀ a s, Entry a s → ∃ (R : callee.State → L.State → Prop)
      (post : callee.Output → L.State → Prop),
      Simulation L.segment callee R post ∧ R (entry a) s ∧ ∀ t, post (result a) t → Done (f a) t) :
    Summary L Entry f Done := by
  intro a s hs
  obtain ⟨R, post, sim, hentry, hdone⟩ := hsim a s hs
  obtain ⟨t, hrun, hpost⟩ := sim.exec (hexec a) hentry
  exact ⟨t, Semantics.segment_exec_iff.mp hrun, hdone t hpost⟩

theorem of_cfg {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat}
    {results : Nat} {callee : Program Op Label signature results}
    {dialect : Dialect Op Value Store}
    (entry : α → CFG.State Value Store Label signature results)
    (result : α → Output Value Store results)
    (hexec : ∀ a, callee.Exec dialect (entry a) (result a))
    (hsim : ∀ a s, Entry a s →
      ∃ (R : CFG.State Value Store Label signature results → L.State → Prop)
        (post : Output Value Store results → L.State → Prop),
        Simulation L.segment (callee.sem dialect) R post ∧ R (entry a) s ∧
          ∀ t, post (result a) t → Done (f a) t) :
    Summary L Entry f Done :=
  of_simulation (callee := callee.sem dialect) entry result (fun a => (hexec a).sem) hsim

theorem call (h : Summary L Entry f Done) {s s₁ : L.State} {a : α} (hpre : L.Reaches s s₁)
    (he : Entry a s₁) {Q : L.State → Prop} (hpost : ∀ t, Done (f a) t → ∃ u, L.Reaches t u ∧ Q u) :
    ∃ u, L.Reaches s u ∧ Q u := by
  obtain ⟨t, ht, hdone⟩ := h a s₁ he
  obtain ⟨u, hu, hq⟩ := hpost t hdone
  exact ⟨u, hpre.trans (ht.trans hu), hq⟩

theorem conseq {Entry' : α → L.State → Prop} {Done' : β → L.State → Prop}
    (h : Summary L Entry f Done) (hentry : ∀ a s, Entry' a s → Entry a s)
    (hdone : ∀ b t, Done b t → Done' b t) : Summary L Entry' f Done' := by
  intro a s hs
  obtain ⟨t, ht, hd⟩ := h a s (hentry a s hs)
  exact ⟨t, ht, hdone _ t hd⟩

theorem matchedBy {Label Value Store : Type} {signature : Label → Nat}
    {results : Nat} {R : CFG.State Value Store Label signature results → L.State → Prop}
    {post : Output Value Store results → L.Output → Prop} (h : Summary L Entry f Done) {a : α}
    {s : L.State} (he : Entry a s) {t : Outcome Value Store Label signature results}
    (hrest : ∀ u, Done (f a) u → t.MatchedBy L R post u) : t.MatchedBy L R post s :=
  let ⟨u, hu, hd⟩ := h a s he
  Outcome.MatchedBy.reaches hu (hrest u hd)

end Summary

end P256.Proofs.CFG
