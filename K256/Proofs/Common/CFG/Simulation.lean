import K256.Proofs.Common.CFG.Lemma.IR
import K256.Proofs.Common.Core.Simulation
namespace K256.Proofs.CFG

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

end Outcome

end Blocks

end K256.Proofs.CFG

namespace K256.Proofs.Simulation

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

end K256.Proofs.Simulation

namespace K256.Proofs.CFG

def Summary (L : Semantics) {α β : Type} (Entry : α → L.State → Prop) (f : α → β)
    (Done : β → L.State → Prop) : Prop :=
  ∀ a s, Entry a s → ∃ t, L.Reaches s t ∧ Done (f a) t

namespace Summary

variable {L : Semantics} {α β : Type} {Entry : α → L.State → Prop} {f : α → β}
  {Done : β → L.State → Prop}

theorem call (h : Summary L Entry f Done) {s s₁ : L.State} {a : α} (hpre : L.Reaches s s₁)
    (he : Entry a s₁) {Q : L.State → Prop} (hpost : ∀ t, Done (f a) t → ∃ u, L.Reaches t u ∧ Q u) :
    ∃ u, L.Reaches s u ∧ Q u := by
  obtain ⟨t, ht, hdone⟩ := h a s₁ he
  obtain ⟨u, hu, hq⟩ := hpost t hdone
  exact ⟨u, hpre.trans (ht.trans hu), hq⟩

end Summary

end K256.Proofs.CFG
