import K256.Proofs.Verify.Transfer.Signature.Agreement

namespace K256.Proofs.Verify.Transfer.Signature
open K256.Proofs.CFG

variable {A B V M : Type} {O : Nat → Type} {r n m : Nat}
variable {pair : A → B → Bool} {live : A → Nat} {ret off mask : Nat}
variable {p : Program O B (fun _ => r) r} {d : Dialect O V M}

def EdgeOK (x : Edge A (fun _ => r) n) (y : Edge B (fun _ => r) m)
    (pair : A → B → Bool) (live : A → Nat) (off mask : Nat) : Bool :=
  pair x.target y.target && (List.finRange r).all fun i =>
    !((live x.target).testBit i.val) || Supports r off mask x.arguments[i].val y.arguments[i].val

def tagsOK (x : Option (Fin n)) (y : Option (Fin m)) (r off mask : Nat) : Bool :=
  match x, y with
  | none, none => true
  | some i, some j => Supports r off mask i.val j.val
  | _, _ => false

def TermOK (x : Terminator A (fun _ => r) r n) (y : Terminator B (fun _ => r) r m)
    (pair : A → B → Bool) (live : A → Nat) (ret off mask : Nat) : Bool :=
  match x, y with
  | .br e, .br f => EdgeOK e f pair live off mask
  | .condBr i a b, .condBr j c e =>
    Supports r off mask i.val j.val && EdgeOK a c pair live off mask && EdgeOK b e pair live off mask
  | .call a c, .call b e =>
    EdgeOK a b pair live off mask && pair c.target e.target && (c.size == 0) && (e.size == 0) &&
    ((List.finRange r).all fun i => !(live c.target).testBit i.val || ret.testBit i.val) &&
    tagsOK c.guard e.guard r off mask
  | .ret a t, .ret b u =>
    ((List.finRange r).all fun i => !ret.testBit i.val || Supports r off mask a[i].val b[i].val) &&
    tagsOK t u r off mask
  | _, _ => false

private theorem supports_register_iff {i j : Fin r} {bits : Nat} :
    Supports r 0 bits i.val j.val = true ↔ i.val = j.val ∧ bits.testBit j.val = true := by
  simp only [Supports, indexAt, available, j.isLt, Nat.not_le.mpr j.isLt, ite_true,
    decide_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq]

private theorem agree_live_selection {a : Values V n} {b : Values V m}
    (h : Agree r off mask a b) {x : Vector (Fin n) r} {y : Vector (Fin m) r} {bits : Nat}
    (ok : ((List.finRange r).all fun i => !bits.testBit i.val ||
      Supports r off mask x[i].val y[i].val) = true) :
    Agree r 0 bits (a.select x) (b.select y) := by
  intro i j support
  obtain ⟨same, liveBit⟩ := supports_register_iff.mp support
  cases Fin.ext same
  change (a.select x)[i.val] = (b.select y)[i.val]
  rw [Values.getElem_select, Values.getElem_select]
  apply h
  have check := List.all_eq_true.mp ok i (List.mem_finRange i)
  simpa only [Fin.getElem_fin, liveBit, Bool.not_true, Bool.false_or] using check

private theorem agree_edge {a : Values V n} {b : Values V m}
    (h : Agree r off mask a b) {x : Edge A (fun _ => r) n} {y : Edge B (fun _ => r) m}
    (ok : EdgeOK x y pair live off mask = true) (s : M) :
    LocAgree pair live (x.eval a s) (y.eval b s) := by
  obtain ⟨labels, arguments⟩ := Bool.and_eq_true_iff.mp ok
  exact ⟨labels, rfl, agree_live_selection h arguments⟩

private theorem agree_tag {a : Values V n} {b : Values V m} (h : Agree r off mask a b)
    {x : Option (Fin n)} {y : Option (Fin m)} (ok : tagsOK x y r off mask = true) :
    x.map (a[·]) = y.map (b[·]) := by
  cases x <;> cases y
  · rfl
  · contradiction
  · contradiction
  · exact congrArg some (h _ _ ok)

theorem matchesTerm {x : Terminator A (fun _ => r) r n} {y : Terminator B (fun _ => r) r m}
    (ok : TermOK x y pair live ret off mask = true)
    {a : Values V n} {b : Values V m} (h : Agree r off mask a b) (s : M) :
    Matches p d (LocAgree pair live) (OutAgree ret) (x.eval d a s) (y.eval d b s) := by
  cases x <;> cases y <;> simp only [TermOK, Bool.and_eq_true, and_assoc] at ok <;> try contradiction
  case br.br =>
    exact .jump (agree_edge h ok s)
  case condBr.condBr i onTrue onFalse j onTrue' onFalse' =>
    obtain ⟨test, trueEdge, falseEdge⟩ := ok
    simp only [Terminator.eval, h i j test]
    split
    · exact .jump (agree_edge h trueEdge s)
    · exact .jump (agree_edge h falseEdge s)
  case call.call callee c callee' e =>
    obtain ⟨edge, target, _, _, liveReturns, guards⟩ := ok
    refine .call (agree_edge h edge s) ?_
    intro left right out accepts
    have guard := agree_tag h guards
    refine ⟨?_, target, out.1, ?_⟩
    · simpa only [StackFrame.Accepts, Cont.eval, guard, out.2.1] using accepts
    · intro i j support
      obtain ⟨same, liveBit⟩ := supports_register_iff.mp support
      change (live c.target).testBit j.val = true at liveBit
      have check := List.all_eq_true.mp liveReturns j (List.mem_finRange j)
      have retBit : ret.testBit j.val = true := by
        simpa only [Fin.getElem_fin, liveBit, Bool.not_true, Bool.false_or] using check
      have returned := out.2.2 i j (supports_register_iff.mpr ⟨same, retBit⟩)
      change ((left.values ++ (c.eval a).kept).cast (c.eval a).arity)[i.val] =
        ((right.values ++ (e.eval b).kept).cast (e.eval b).arity)[j.val]
      simpa only [Fin.getElem_fin, Vector.getElem_cast, Vector.getElem_append_left i.isLt,
        Vector.getElem_append_left j.isLt] using returned
  case ret.ret =>
    exact .ret ⟨rfl, agree_tag h ok.2, agree_live_selection h ok.1⟩

end K256.Proofs.Verify.Transfer.Signature
