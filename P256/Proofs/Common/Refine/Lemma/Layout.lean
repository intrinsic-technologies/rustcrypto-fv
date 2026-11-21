import P256.Proofs.Common.Refine.Layout
import P256.Proofs.Common.CFG.Eval
import P256.Proofs.Common.Lift.Lemma.Reg

namespace P256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift Prelude

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

theorem Ahead.here {l : lifted.Location} (h : E l) : Ahead lifted code E l := ⟨l, .refl l, h⟩

theorem Ahead.of_step {l : lifted.Location}
    (hfin : ∀ l', fin (lifted.program.runBlock (dialect code) l') → E l')
    (h : Onward lifted code E fin (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code E l := by
  cases hs : lifted.program.runBlock (dialect code) l with
  | jump l' =>
    rw [hs] at h
    obtain ⟨l'', hr, he⟩ := h
    exact ⟨l'', .jump hs hr, he⟩
  | call l' fr => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩
  | returned o => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩
  | stuck => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩

theorem Ahead.of_step_jump {l : lifted.Location}
    (h : Onward lifted code E (fun _ => False) (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code E l :=
  Ahead.of_step (fun _ h => h.elim) h

theorem Ahead.of_step_call {Q : lifted.Location → lifted.StackFrame → Prop} {l : lifted.Location}
    (h : Onward lifted code (fun l' => CallTo Q (lifted.program.runBlock (dialect code) l'))
      (CallTo Q)
      (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code (fun l' => CallTo Q (lifted.program.runBlock (dialect code) l')) l :=
  Ahead.of_step (fun _ h => h) h

theorem Ahead.of_step_ret {Q : Output Value Ram Reg.count → Prop} {l : lifted.Location}
    (h : Onward lifted code (fun l' => ReturnOf Q (lifted.program.runBlock (dialect code) l'))
      (ReturnOf Q)
      (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code (fun l' => ReturnOf Q (lifted.program.runBlock (dialect code) l')) l :=
  Ahead.of_step (fun _ h => h) h

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

theorem Layout.matches_jump {u : Location UValue UStore ULabel usig} :
    L.MatchedBy code c l (.jump u) = Ahead lifted code (L.Rel code c u) l := rfl

theorem Layout.matches_call {u : Location UValue UStore ULabel usig}
    {uf : CFG.StackFrame UValue ULabel usig results} :
    L.MatchedBy code c l (.call u uf) = Ahead lifted code (fun l' => CallTo (fun l'' lf =>
      ∃ c', L.Rel code c' u l'' ∧ L.Resumes code c' c uf lf)
        (lifted.program.runBlock (dialect code) l')) l :=
  rfl

theorem Layout.matches_returned {uo : Output UValue UStore results} :
    L.MatchedBy code c l (.returned uo) =
      Ahead lifted code
        (fun l' => ReturnOf (L.RetRel code c uo) (lifted.program.runBlock (dialect code) l')) l :=
  rfl

theorem Layout.matches_stuck : L.MatchedBy code c l .stuck := trivial

theorem Layout.matches_ite {b : Prop} [Decidable b]
    {x y : Transfer UValue UStore ULabel usig results}
    (hx : b → L.MatchedBy code c l x) (hy : ¬b → L.MatchedBy code c l y) :
    L.MatchedBy code c l (if b then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

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

theorem args_eq_vars (v : Vector Value Reg.count) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
      a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39
      a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 : Value,
      v = ⟨(a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 ::
        a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 ::
        a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 ::
        a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 :: a52 ::
        []).toArray, rfl⟩ := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 ::
      a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 :: a27 ::
      a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 :: a40 ::
      a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 :: a52 :: [], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
      a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47,
      a48, a49, a50, a51, a52, rfl⟩

@[elab_as_elim] theorem args_cases {motive : Vector Value Reg.count → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46
      a47 a48 a49 a50 a51 a52 : Value,
      motive ⟨(a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 ::
        a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 ::
        a26 :: a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 ::
        a39 :: a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 ::
        a52 :: []).toArray, rfl⟩)
    (v : Vector Value Reg.count) : motive v := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
    a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47,
    a48, a49, a50, a51, a52, rfl⟩ := args_eq_vars v
  exact h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _

end P256.Proofs.Refine
