import K256.Proofs.Ecdh.Transfer.Operands

namespace K256.Proofs.Verify.Transfer.Padding

open CFG

variable {Op : Nat → Type} {Label Value Store : Type} {k r : Nat}

structure Site (Op : Nat → Type) (Label : Type) (k : Nat) where
  op : Op 0
  target : Label
  arguments : Vector (Fin (k + 1)) k

def Site.prefix (s : Site Op Label k) : Block Op Label (fun _ => k) r k :=
  .letOp s.op #v[] (.terminate (.br ⟨s.target, s.arguments⟩))

def Site.join (s : Site Op Label k) (p : Program Op Label (fun _ => k) r) :
    Block Op Label (fun _ => k) r k :=
  .letOp s.op #v[] (Ecdh.Transfer.mapOperands (fun i : Fin k => s.arguments[i]) (p.blocks s.target))

def join (p : Program Op Label (fun _ => k) r) (sites : Label → Option (Site Op Label k)) :
    Program Op Label (fun _ => k) r where
  blocks l := match sites l with
    | none => p.blocks l
    | some site => site.join p

private def Follows (p : Program Op Label (fun _ => k) r) (d : Dialect Op Value Store)
    (s : State Value Store Label (fun _ => k) r) : Outcome Value Store Label (fun _ => k) r → Prop
  | .done o => p.Exec d s o
  | .next t => ∀ {o}, p.Exec d t o → p.Exec d s o
  | .stuck => True

private theorem followsStep (p : Program Op Label (fun _ => k) r) (d : Dialect Op Value Store)
    (s : State Value Store Label (fun _ => k) r) : Follows p d s (p.step d s) := by
  cases h : p.step d s with
  | done => exact .done h
  | next => exact .next h
  | stuck => trivial

private theorem followsJoin (p : Program Op Label (fun _ => k) r) (d : Dialect Op Value Store)
    (sites : Label → Option (Site Op Label k))
    (blocks : ∀ l site, sites l = some site → p.blocks l = site.prefix)
    (s : State Value Store Label (fun _ => k) r) : Follows p d s ((join p sites).step d s) := by
  obtain ⟨⟨l, a, m⟩, stk⟩ := s
  cases h : sites l with
  | none =>
    simpa only [Program.step, Program.runBlock, join, h] using
      followsStep p d ⟨⟨l,a,m⟩,stk⟩
  | some site =>
    have args : Vector.ofFn (fun i : Fin k => site.arguments[i]) = site.arguments := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      rfl
    cases e : d.eval site.op (a.select #v[]) m with
    | none => simp only [Program.step, Program.runBlock, join, h, Site.join, Block.eval, e,
                         Transfer.next, Follows]
    | some res =>
      obtain ⟨v,m'⟩ := res
      let t : State Value Store Label (fun _ => k) r :=
        ⟨⟨site.target, Values.select (a.push v) site.arguments, m'⟩, stk⟩
      have first : p.step d ⟨⟨l,a,m⟩,stk⟩ = .next t := by
        simp only [Program.step, Program.runBlock, blocks _ _ h, Site.prefix, Block.eval, e,
          Terminator.eval, Edge.eval, Transfer.next, t]
      have same : (join p sites).step d ⟨⟨l,a,m⟩,stk⟩ = p.step d t := by
        simp only [Program.step, Program.runBlock, join, h, Site.join, Block.eval, e,
          Ecdh.Transfer.eval_mapOperands, args, t]
      rw [same]
      cases ht : p.step d t with
      | done => exact .next first (.done ht)
      | next => exact fun {_} run => .next first (.next ht run)
      | stuck => trivial

theorem exec {p : Program Op Label (fun _ => k) r} {d : Dialect Op Value Store}
    {sites : Label → Option (Site Op Label k)}
    (blocks : ∀ l site, sites l = some site → p.blocks l = site.prefix)
    {s : State Value Store Label (fun _ => k) r} {out : Output Value Store r}
    (run : (join p sites).Exec d s out) : p.Exec d s out := by
  induction run with
  | @done state _ h =>
    have f := followsJoin p d sites blocks state
    rw [h] at f
    exact f
  | @next state _ _ h _ ih =>
    have f := followsJoin p d sites blocks state
    rw [h] at f
    exact f ih

end K256.Proofs.Verify.Transfer.Padding
