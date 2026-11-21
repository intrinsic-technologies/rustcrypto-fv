import K256.Proofs.Common.Refine.Layout
import K256.Proofs.Common.CFG.Eval
import K256.Proofs.Common.Lift.Lemma.Reg
namespace K256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift Prelude

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}
  {code : CodeMap}

theorem JumpRun.reaches {l l' : lifted.Location} (h : JumpRun lifted code l l')
    (stack : List lifted.StackFrame) :
    (lifted.program.sem (dialect code)).Reaches ⟨l, stack⟩ ⟨l', stack⟩ := by
  induction h with
  | refl => exact .refl _
  | jump hs _ ih =>
    refine .step ?_ ih
    show (lifted.program.runBlock (dialect code) _).next (dialect code) stack = _
    rw [hs]
    rfl

section Run

variable {E : lifted.Location → Prop}
  {fin : Transfer Value Ram lifted.Label signature Reg.count → Prop}

theorem Onward.jump {l : lifted.Location} (h : Ahead lifted code E l) :
    Onward lifted code E fin (.jump l) := h
theorem Onward.call {l : lifted.Location} {fr : lifted.StackFrame} (h : fin (.call l fr)) :
    Onward lifted code E fin (.call l fr) := h
theorem Onward.returned {o : Output Value Ram Reg.count} (h : fin (.returned o)) :
    Onward lifted code E fin (.returned o) := h

theorem Onward.guard {g : Prop} [Decidable g]
    {x : Transfer Value Ram lifted.Label signature Reg.count} (hg : g)
    (h : Onward lifted code E fin x) : Onward lifted code E fin (if g then x else .stuck) := by
  simp only [hg, ↓reduceIte]
  exact h

theorem Onward.ite {c : Prop} [Decidable c]
    {x y : Transfer Value Ram lifted.Label signature Reg.count}
    (hx : c → Onward lifted code E fin x) (hy : ¬c → Onward lifted code E fin y) :
    Onward lifted code E fin (if c then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

end Run

theorem CallTo.intro {Q : lifted.Location → lifted.StackFrame → Prop} {l : lifted.Location}
    {fr : lifted.StackFrame} (h : Q l fr) :
    CallTo Q (.call l fr) := h
theorem ReturnOf.intro {Q : Output Value Ram Reg.count → Prop} {o : Output Value Ram Reg.count}
    (h : Q o) : ReturnOf (lifted := lifted) Q (.returned o) := h

section MatchedBy

variable {L : Layout P D lifted Ctx} {c : Ctx} {l : lifted.Location}

end MatchedBy

section Holds

variable (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)

@[refine_layout] theorem holds_reg (r : Fin Reg.count) (v : Value) :
    (Atom.reg r v).Holds code args mem = (args[r] = v) := rfl
@[refine_layout] theorem holds_low (r : Fin Reg.count) (w : Nat) (v : BitVec w) :
    (Atom.low r w v).Holds code args mem = (args[r].get w = v) := rfl
@[refine_layout] theorem holds_mem (a : BitVec 64) (w : Nat) (v : BitVec w) :
    (Atom.mem a w v).Holds code args mem = (memLoad mem a w = v) := rfl
@[refine_layout] theorem holds_words (a : BitVec 64) (w : Nat) {n : Nat}
    (vs : Vector (BitVec w) n) : (Atom.words a w vs).Holds code args mem = WordsAt mem a w vs := rfl
@[refine_layout] theorem holds_readable (a : BitVec 64) (len : Nat) :
    (Atom.readable a len).Holds code args mem = Readable mem a len := rfl
@[refine_layout] theorem holds_writable (a : BitVec 64) (len : Nat) :
    (Atom.writable a len).Holds code args mem = Writable code mem a len := rfl
@[refine_layout] theorem holds_fact (p : Prop) : (Atom.fact p).Holds code args mem = p := rfl
@[refine_layout] theorem all_nil : Atom.All code args mem [] = True := rfl
@[refine_layout] theorem all_cons (a : Atom) (as : List Atom) :
    Atom.All code args mem (a :: as) = (a.Holds code args mem ∧ Atom.All code args mem as) := rfl

end Holds

theorem Atom.all_append {args : Values Value Reg.count} {mem : Ram} :
    ∀ as bs : List Atom, Atom.All code args mem (as ++ bs) ↔
      Atom.All code args mem as ∧ Atom.All code args mem bs
  | [], _ => by simp [Atom.All]
  | a :: as, bs => by
    simp only [List.cons_append, Atom.All, Atom.all_append as bs, and_assoc]

attribute [refine_layout] Atom.gpr List.cons_append List.nil_append List.append_nil
end K256.Proofs.Refine
