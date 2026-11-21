import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Layout

namespace ChaCha20Poly1305.Proofs.Decrypt
open ChaCha20Poly1305.Proofs.CFG

section
variable {Op : Nat → Type} {Label Value Store : Type} {sig : Label → Nat} {n : Nat}
  (p : Program Op Label sig n) (d : Dialect Op Value Store)

inductive Returns : Location Value Store Label sig → Output Value Store n → Prop where
  | ret {l o} (h : p.runBlock d l = .returned o) : Returns l o
  | jump {l l' o} (h : p.runBlock d l = .jump l') (tail : Returns l' o) : Returns l o
  | call {l f k t o} (h : p.runBlock d l = .call f k)
      (callee : Returns f t) (accept : k.Accepts d t.tag = true)
      (caller : Returns (k.resume t) o) : Returns l o

variable {p d}

theorem Returns.execWith {l o} (h : Returns p d l o) {stack} {final}
    (k : (Transfer.returned o).next d stack = .done final ∨
      ∃ s', (Transfer.returned o).next d stack = .next s' ∧ p.Exec d s' final) :
    p.Exec d ⟨l,stack⟩ final := by
  induction h generalizing stack final with
  | ret h =>
    rcases k with k | ⟨s', k, tail⟩
    · exact .done (by simpa only [Program.step, h] using k)
    · exact .next (by simpa only [Program.step, h] using k) tail
  | jump h _ ih =>
    exact .next (by simp only [Program.step, h, Transfer.next]) (ih k)
  | @call l f fr t o h _ accept _ ihF ihK =>
    refine .next (by simp only [Program.step, h, Transfer.next]) (ihF (stack := fr :: stack) (Or.inr ?_))
    exact ⟨_, by simp only [Transfer.next,accept,ite_true], ihK k⟩

theorem Returns.exec {l o} (h : Returns p d l o) : p.Exec d ⟨l,[]⟩ o :=
  h.execWith (Or.inl rfl)

private theorem bindStack {s s' : State Value Store Label sig n} (tail : List (StackFrame Value Label sig n))
    (hs : p.step d s = .next s') :
    p.step d ⟨s.location,s.stack ++ tail⟩ = .next ⟨s'.location,s'.stack ++ tail⟩ := by
  rcases s with ⟨l,ss⟩
  rcases s' with ⟨l',ss'⟩
  unfold Program.step at *
  cases hb : p.runBlock d l with
  | jump l' => simp_all [Transfer.next]
  | call v f => simp_all [Transfer.next]; rw [← hs.2]; rfl
  | stuck => simp_all [Transfer.next]
  | returned o =>
    cases ss with
    | nil => simp_all [Transfer.next]
    | cons fr st =>
      simp only [hb, Transfer.next] at hs
      split at hs <;> simp_all [Transfer.next]

theorem execCall {l f k o r} (h : p.runBlock d l = .call f k)
    (callee : p.Exec d ⟨f,[]⟩ r) (accept : k.Accepts d r.tag = true)
    (caller : p.Exec d ⟨k.resume r,[]⟩ o) : p.Exec d ⟨l,[]⟩ o := by
  refine .next (next := ⟨f,[k]⟩) (by simp only [Program.step,h,Transfer.next]) ?_
  generalize eqS : (⟨f,[]⟩ : State Value Store Label sig n) = s at callee
  suffices p.Exec d ⟨s.location,s.stack ++ [k]⟩ o by subst s; exact this
  clear eqS h
  induction callee with
  | @done s r h =>
    rcases s with ⟨l,ss⟩
    unfold Program.step at h
    cases hb : p.runBlock d l <;> simp only [hb,Transfer.next] at h
    case returned t =>
      cases ss with
      | nil =>
        cases h
        exact .next (by simp [Program.step, hb, Transfer.next, accept]) caller
      | cons fr rest =>
        dsimp only at h
        split at h <;> cases h
    all_goals cases h
  | next h _ ih => exact .next (bindStack _ h) (ih accept caller)
end

end ChaCha20Poly1305.Proofs.Decrypt
