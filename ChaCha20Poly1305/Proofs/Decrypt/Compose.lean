import ChaCha20Poly1305.Proofs.Decrypt.Exec

namespace ChaCha20Poly1305.Proofs.Decrypt
open X86 X86.Machine X86.UserProcess ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine

variable {lifted : Lifted} {code : CodeMap}
  {Op : Nat → Type} {Label V S Ctx : Type} {sig : Label → Nat} {n : Nat}
  {pr : Program Op Label sig n} {d : Dialect Op V S} (lay : Layout pr d lifted Ctx)

theorem execJump {a b : lifted.Location} {o} (h : JumpRun lifted code a b)
    (e : lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨b,[]⟩ o) :
    lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨a,[]⟩ o := by
  induction h with
  | refl => exact e
  | jump h _ ih => exact .next (by simp only [Program.step,h,Transfer.next]) (ih e)

theorem execAhead {a : lifted.Location} {P : lifted.Location → Prop} {o}
    (h : Ahead lifted code P a)
    (k : ∀ b, P b → lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨b,[]⟩ o) :
    lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨a,[]⟩ o := by
  obtain ⟨b, hb, hh⟩ := h
  exact execJump hb (k b hh)

theorem composeReturn {c a u} (h : lay.MatchedBy code c a (.returned u)) :
    ∃ o, lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨a,[]⟩ o ∧ lay.RetRel code c u o := by
  obtain ⟨b, hb, hh⟩ := h
  cases he : lifted.program.runBlock (ChaCha20Poly1305.Proofs.Lift.dialect code) b with
  | returned o =>
    rw [he] at hh
    exact ⟨o, execJump hb (.done (by simp only [Program.step,he,Transfer.next])), hh⟩
  | jump v | call f k | stuck => rw [he] at hh; exact False.elim hh

theorem composeCall {c a u uf} (h : lay.MatchedBy code c a (.call u uf))
    {ret : Output V S n}
    (accept : uf.Accepts d ret.tag = true)
    (callee : ∀ ctx callee, lay.Rel code ctx u callee → ∃ o,
      lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨callee,[]⟩ o ∧ lay.RetRel code ctx ret o)
    {post : Output Value Ram Reg.count → Prop}
    (caller : ∀ b, lay.Rel code c (uf.resume ret) b →
      ∃ out, lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨b,[]⟩ out ∧ post out) :
    ∃ out, lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect code) ⟨a,[]⟩ out ∧ post out := by
  obtain ⟨b, hb, hh⟩ := h
  cases he : lifted.program.runBlock (ChaCha20Poly1305.Proofs.Lift.dialect code) b with
  | call dest fr =>
    rw [he] at hh
    obtain ⟨ctx, rel, resumes⟩ := hh
    obtain ⟨o, ho, hres⟩ := callee ctx dest rel
    obtain ⟨ok, follow⟩ := resumes ret o hres accept
    obtain ⟨out, run, good⟩ := caller _ follow
    exact ⟨out, execJump hb (execCall he ho ok run), good⟩
  | jump v | returned v | stuck => rw [he] at hh; exact False.elim hh

end ChaCha20Poly1305.Proofs.Decrypt
