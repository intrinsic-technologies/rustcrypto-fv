import K256.Proofs.Verify.Transfer.Signature.Terminators

namespace K256.Proofs.Verify.Transfer.Signature

open K256.Proofs.CFG

variable {A B V M : Type} {O : Nat → Type} {r n m : Nat}
variable {pair : A → B → Bool} {live : A → Nat} {ret off mask : Nat}
variable {p : Program O B (fun _ => r) r} {d : Dialect O V M}

theorem agreePush {a : Values V n} {b : Values V m}
    (h : Agree r off mask a b) (len : n = m + off) (bound : r ≤ m) (v : V) :
    Agree r off mask (a.push v) (b.push v) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hsym
  have hij : i = indexAt r off j := by
    simpa only [Supports, Bool.and_eq_true, beq_iff_eq] using
      (show (i == indexAt r off j) = true from (Bool.and_eq_true_iff.mp hsym).1)
  by_cases he : j = m
  · subst j
    have : i = n := by simpa [indexAt, Nat.not_lt.mpr bound, len] using hij
    change (a.push v)[i] = (b.push v)[m]
    simp only [this, Vector.getElem_push_last]
  · have hjm : j < m := by omega
    have hin : i < n := by unfold indexAt at hij; split at hij <;> omega
    change (a.push v)[i] = (b.push v)[j]
    rw [Vector.getElem_push_lt hin, Vector.getElem_push_lt hjm]
    exact h ⟨i, hin⟩ ⟨j, hjm⟩ hsym

def operandsOK {k t : Nat} (x : Vector (Fin n) k) (y : Vector (Fin m) t)
    (r off mask : Nat) : Bool :=
  (x.toList.zip y.toList).all fun ij => Supports r off mask ij.1.val ij.2.val

theorem agreeSelect {k : Nat} {a : Values V n} {b : Values V m}
    (h : Agree r off mask a b) (x : Vector (Fin n) k) (y : Vector (Fin m) k)
    (ok : operandsOK x y r off mask = true) : a.select x = b.select y := by
  apply Vector.ext
  intro i hi
  rw [Values.getElem_select, Values.getElem_select]
  apply h
  exact List.all_eq_true.mp ok (x[i], y[i]) (by
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩)

def operations {L : Type} : {n : Nat} → Block O L (fun _ => r) r n → List (Sigma O)
  | _, .letOp op _ next => ⟨_, op⟩ :: operations next
  | _, .terminate _ => []

def blocksOK (pair : A → B → Bool) (live : A → Nat) (ret off mask : Nat) :
    {n m : Nat} → Block O A (fun _ => r) r n → Block O B (fun _ => r) r m → Bool
  | _, _, .letOp _ x s, .letOp _ y t =>
    operandsOK x y r off mask && blocksOK pair live ret off mask s t
  | _, _, .terminate x, .terminate y => TermOK x y pair live ret off mask
  | _, _, _, _ => false

def BlockMatches (p : Program O B (fun _ => r) r) (d : Dialect O V M)
    (pair : A → B → Bool) (live : A → Nat) (ret off mask : Nat)
    (s : Block O A (fun _ => r) r n) (t : Block O B (fun _ => r) r m) : Prop :=
  ∀ a b, Agree r off mask a b → ∀ mem,
    Matches p d (LocAgree pair live) (OutAgree ret) (s.eval d a mem) (t.eval d b mem)

theorem matchesLet {k : Nat} {op : O k} {x : Vector (Fin n) k} {y : Vector (Fin m) k}
    {s : Block O A (fun _ => r) r (n+1)} {t : Block O B (fun _ => r) r (m+1)}
    (len : n = m + off) (bound : r ≤ m) (ok : operandsOK x y r off mask = true)
    (next : BlockMatches p d pair live ret off mask s t) :
    BlockMatches p d pair live ret off mask (.letOp op x s) (.letOp op y t) := by
  intro a b h mem
  simp only [Block.eval, agreeSelect h x y ok]
  split
  · exact next _ _ (agreePush h len bound _) _
  · exact .stuck

theorem matchesBlocks {s : Block O A (fun _ => r) r n} {t : Block O B (fun _ => r) r m}
    (len : n = m + off) (bound : r ≤ m)
    (ops : operations s = operations t) (ok : blocksOK pair live ret off mask s t = true) :
    BlockMatches p d pair live ret off mask s t := by
  induction s generalizing m with
  | letOp op x s ih =>
    cases t with
    | terminate y => contradiction
    | letOp op' y t =>
      obtain ⟨hop, hops⟩ := List.cons.inj ops
      obtain ⟨hk, he⟩ := Sigma.mk.inj hop
      subst hk
      cases eq_of_heq he
      obtain ⟨hx,ht⟩ := Bool.and_eq_true_iff.mp ok
      exact matchesLet len bound hx (ih (by omega) (by omega) hops ht)
  | terminate x =>
    cases t with
    | letOp => contradiction
    | terminate y => exact fun _ _ h mem => matchesTerm ok h mem

theorem matchesJumpBoundary {s : Block O A (fun _ => r) r n}
    {e : Edge B (fun _ => r) m} {skip : Nat}
    (ok : ((List.finRange r).all fun j => !(mask.testBit j.val) ||
      Supports r off mask j.val e.arguments[j.val].val) = true)
    (next : BlockMatches p d pair live ret skip mask s (p.blocks e.target)) :
    BlockMatches p d pair live ret off mask s (.terminate (.br e)) := by
  intro a b h mem
  apply Matches.advance
  apply next
  intro i j hij
  change a[i] = (b.select e.arguments)[j.val]
  rw [Values.getElem_select]
  have hs : i.val = j.val ∧ mask.testBit j.val = true := by
    simpa [Supports, available, indexAt, j.isLt, Nat.not_le.mpr j.isLt] using hij
  apply h
  have hc := List.all_eq_true.mp ok j (List.mem_finRange j)
  simpa only [hs.1, hs.2, Bool.not_true, Bool.false_or] using hc

end K256.Proofs.Verify.Transfer.Signature
