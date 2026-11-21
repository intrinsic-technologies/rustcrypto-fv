import K256.Proofs.Common.CFG.Lemma.IR

namespace K256.Proofs.Ecdh.Transfer
open CFG

private def extend {n m : Nat} (f : Fin n → Fin m) (i : Fin (n + 1)) : Fin (m + 1) :=
  if h : i.val < n then (f ⟨i.val, h⟩).castSucc else Fin.last m

private def mapTerm {Label : Type} {sig : Label → Nat} {r n m : Nat}
    (f : Fin n → Fin m) : Terminator Label sig r n → Terminator Label sig r m
  | .br e => .br ⟨e.target, e.arguments.map f⟩
  | .condBr c t e => .condBr (f c) ⟨t.target, t.arguments.map f⟩ ⟨e.target, e.arguments.map f⟩
  | .call c k => .call ⟨c.target, c.arguments.map f⟩ ⟨k.target, k.kept.map f, k.arity, k.guard.map f⟩
  | .ret v t => .ret (v.map f) (t.map f)

def mapOperands {Op : Nat → Type} {Label : Type} {sig : Label → Nat} {r n m : Nat}
    (f : Fin n → Fin m) : Block Op Label sig r n → Block Op Label sig r m
  | .letOp op args rest => .letOp op (args.map f) (mapOperands (extend f) rest)
  | .terminate t => .terminate (mapTerm f t)

theorem eval_mapOperands {Op : Nat → Type} {Label Value Store : Type} {sig : Label → Nat}
    {r n m : Nat} (b : Block Op Label sig r n) (d : Dialect Op Value Store)
    (f : Fin n → Fin m) (a : Values Value m) (s : Store) :
    (mapOperands f b).eval d a s = b.eval d (a.select (Vector.ofFn f)) s := by
  suffices ∀ (v : Values Value n), (∀ i : Fin n, a[f i] = v[i]) →
      (mapOperands f b).eval d a s = b.eval d v s by
    apply this
    intro i
    change a[(f i).val] = (a.select (Vector.ofFn f))[i.val]
    simp only [Values.getElem_select, Vector.getElem_ofFn]
    rfl
  induction b generalizing m s with
  | letOp op args rest ih =>
    rename_i size argc
    intro v h
    have select_eq : a.select (args.map f) = v.select args := by
      apply Vector.ext
      intro i hi
      simp only [Values.getElem_select, Vector.getElem_map, h]
    simp only [mapOperands, Block.eval, select_eq]
    split
    · rename_i value _ _
      apply ih
      intro i
      by_cases hi : i.val < size
      · have eq : extend f i = (f ⟨i.val, hi⟩).castSucc := by simp only [extend, dite_eq_left hi]
        refine (congrArg (fun j : Fin _ => (a.push value)[j]) eq).trans ?_
        exact (Vector.getElem_push_lt (f ⟨i.val, hi⟩).isLt).trans
          ((h ⟨i.val, hi⟩).trans (Vector.getElem_push_lt hi).symm)
      · have eq : extend f i = Fin.last m := by simp only [extend, dite_eq_right hi]
        have ilast : i = Fin.last size := Fin.ext (by
          change i.val = size
          have := i.isLt
          omega)
        refine (congrArg (fun j : Fin _ => (a.push value)[j]) eq).trans ?_
        exact Vector.getElem_push_last.trans (
          ((congrArg (fun j : Fin _ => (v.push value)[j]) ilast).trans Vector.getElem_push_last).symm)
    · rfl
  | terminate t =>
    intro v h
    have select_eq {c : Nat} (args : Vector (Fin _) c) : a.select (args.map f) = v.select args := by
      apply Vector.ext
      intro i hi
      simp only [Values.getElem_select, Vector.getElem_map, h]
    cases t <;>
      simp only [mapOperands, mapTerm, Block.eval, Terminator.eval, Edge.eval, Cont.eval,
        select_eq, h, Option.map_map, Function.comp_def]

end K256.Proofs.Ecdh.Transfer
