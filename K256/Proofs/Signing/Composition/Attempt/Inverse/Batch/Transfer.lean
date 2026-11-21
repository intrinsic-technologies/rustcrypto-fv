import K256.Proofs.Signing.Transfer.Generator.Blocks

namespace K256.Proofs.Signing.Composition.Attempt.Inverse.Batch

open CFG Lift X86.Machine X86.UserProcess X86Proofs
open Generate.Serialize Verify.Transfer

private theorem joinedStep {Op : Nat → Type} {L V M : Type} {k r : Nat}
    (p : Program Op L (fun _ => k) r) (d : Dialect Op V M)
    (sites : L → Option (Padding.Site Op L k))
    (prefixBlock : ∀ l site, sites l = some site → p.blocks l = site.prefix)
    (s : State V M L (fun _ => k) r) :
    (Padding.join p sites).step d s = p.step d s ∨
      ∃ t, p.step d s = .next t ∧ (Padding.join p sites).step d s = p.step d t := by
  obtain ⟨⟨l,a,m⟩,stk⟩ := s
  cases h : sites l with
  | none => exact Or.inl (by simp only [Program.step, Program.runBlock, Padding.join, h])
  | some site =>
    cases e : d.eval site.op (a.select #v[]) m with
    | none =>
      left
      simp only [Program.step, Program.runBlock, Padding.join, h, Padding.Site.join, Block.eval,
        prefixBlock _ _ h, Padding.Site.prefix, e]
    | some res =>
      obtain ⟨v,m'⟩ := res
      right
      refine ⟨⟨⟨site.target, Values.select (a.push v) site.arguments, m'⟩,stk⟩, ?_, ?_⟩
      · simp only [Program.step, Program.runBlock, prefixBlock _ _ h, Padding.Site.prefix, Block.eval,
          e, Terminator.eval, Edge.eval, Transfer.next]
      · have args : Vector.ofFn (fun i : Fin k => site.arguments[i]) = site.arguments := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_ofFn]
          rfl
        simp only [Program.step, Program.runBlock, Padding.join, h, Padding.Site.join, Block.eval,
          e, Ecdh.Transfer.eval_mapOperands, args]

private theorem execJoined {Op : Nat → Type} {L V M : Type} {k r : Nat}
    {p : Program Op L (fun _ => k) r} {d : Dialect Op V M} {sites : L → Option (Padding.Site Op L k)}
    (prefixBlock : ∀ l site, sites l = some site → p.blocks l = site.prefix)
    {s : State V M L (fun _ => k) r} {out : Output V M r} (run : p.Exec d s out) :
    (Padding.join p sites).Exec d s out := by
  let q := Padding.join p sites
  suffices q.Exec d s out ∧ ∀ t, q.step d t = p.step d s → q.Exec d t out from this.1
  induction run with
  | @done s out h =>
    have same (t) (eq : q.step d t = p.step d s) : q.Exec d t out := .done (eq.trans h)
    refine ⟨?_, same⟩
    rcases joinedStep p d sites prefixBlock s with eq | ⟨_, next, _⟩
    · exact same s eq
    · rw [h] at next; cases next
  | @next s u out h _ ih =>
    have same (t) (eq : q.step d t = p.step d s) : q.Exec d t out := .next (eq.trans h) ih.1
    refine ⟨?_, same⟩
    rcases joinedStep p d sites prefixBlock s with eq | ⟨v, next, eq⟩
    · exact same s eq
    · rw [h] at next
      cases next
      exact ih.2 s eq

private theorem execBeforeRelabel {A B V M : Type} {O : Nat → Type} {k r : Nat}
    {src : Program O A (fun _ => k) r} {dst : Program O B (fun _ => k) r}
    {f : A → Option B} {d : Dialect O V M}
    (blocks : ∀ a b, f a = some b → Relabel.block f (src.blocks a) = Relabel.block some (dst.blocks b))
    {x : State V M A (fun _ => k) r} {y : State V M B (fun _ => k) r}
    {out : Output V M r} (run : dst.Exec d y out) (hm : Relabel.state f x = Relabel.state some y) :
    src.Exec d x out := by
  have step {x : State V M A (fun _ => k) r} {y : State V M B (fun _ => k) r}
      (h : Relabel.state f x = Relabel.state some y) :
      Relabel.outcome f (src.step d x) = Relabel.outcome some (dst.step d y) := by
    rcases x with ⟨⟨a,u,m⟩,st⟩
    rcases y with ⟨⟨b,v,n⟩,tt⟩
    simp only [Relabel.state, Relabel.location, State.mk.injEq, Location.mk.injEq] at h
    obtain ⟨⟨hl, rfl, rfl⟩, hs⟩ := h
    simp only [Program.step, Program.runBlock, ← Relabel.next_transfer, ← Relabel.eval_block, blocks a b hl, hs]
  induction run generalizing x with
  | done h =>
    have eq := step hm
    rw [h] at eq
    cases e : src.step d x <;> rw [e] at eq <;> cases eq
    exact .done e
  | next h _ ih =>
    have eq := step hm
    rw [h] at eq
    cases e : src.step d x <;> rw [e] at eq
    case next => exact .next e (ih (Outcome.next.inj eq))
    all_goals cases eq

theorem generateModularShift {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : Verify.LIR.program.Exec (dialect code) ⟨⟨.l108980,a,m⟩,[]⟩ out) :
    Generate.LIR.program.Exec (dialect code) ⟨⟨.l108980,a,m⟩,[]⟩ out := by
  apply execBeforeRelabel Signing.Transfer.Generator.blocks
    (execJoined Signing.Transfer.Generator.paddingPrefix run)
  rfl

end K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
