import K256.Proofs.Common.CFG.IR

namespace K256.Proofs.Generate.Serialize.Relabel

open CFG

variable {A B V S : Type} {O : Nat → Type} {k r : Nat}

def term (f : A → B) {n : Nat} : Terminator A (fun _ => k) r n → Terminator B (fun _ => k) r n
  | .br e => .br ⟨f e.target, e.arguments⟩
  | .condBr c e d => .condBr c ⟨f e.target, e.arguments⟩ ⟨f d.target, d.arguments⟩
  | .call e c => .call ⟨f e.target, e.arguments⟩ ⟨f c.target, c.kept, c.arity, c.guard⟩
  | .ret vs tag => .ret vs tag

def block (f : A → B) {n : Nat} :
    Block O A (fun _ => k) r n → Block O B (fun _ => k) r n
  | .letOp op args next => .letOp op args (block f next)
  | .terminate t => .terminate (term f t)

def location (f : A → B) (x : Location V S A (fun _ => k)) : Location V S B (fun _ => k) :=
  ⟨f x.label, x.arguments, x.store⟩

def frame (f : A → B) (x : StackFrame V A (fun _ => k) r) : StackFrame V B (fun _ => k) r :=
  ⟨f x.target, x.kept, x.arity, x.guard⟩

def state (f : A → B) (x : State V S A (fun _ => k) r) : State V S B (fun _ => k) r :=
  ⟨location f x.location, x.stack.map (frame f)⟩

def transfer (f : A → B) : Transfer V S A (fun _ => k) r → Transfer V S B (fun _ => k) r
  | .jump p => .jump (location f p)
  | .call p c => .call (location f p) (frame f c)
  | .returned o => .returned o
  | .stuck => .stuck

def outcome (f : A → B) : Outcome V S A (fun _ => k) r → Outcome V S B (fun _ => k) r
  | .next s => .next (state f s)
  | .done o => .done o
  | .stuck => .stuck

theorem eval_block (f : A → B) (d : Dialect O V S) {n : Nat}
    (b : Block O A (fun _ => k) r n) (v : Values V n) (s : S) :
    (block f b).eval d v s = transfer f (b.eval d v s) := by
  induction b generalizing s with
  | letOp op args next ih =>
    simp only [block, Block.eval]
    split
    · apply ih
    · rfl
  | terminate t =>
    cases t <;> first | rfl | simp only [block, term, Block.eval, Terminator.eval]; split <;> rfl

theorem next_transfer (f : A → B) (d : Dialect O V S)
    (t : Transfer V S A (fun _ => k) r) (stack : List (StackFrame V A (fun _ => k) r)) :
    (transfer f t).next d (stack.map (frame f)) = outcome f (t.next d stack) := by
  cases t with
  | returned o =>
    cases stack with
    | nil => rfl
    | cons hd tl =>
      change (if hd.Accepts d o.tag then _ else _) = outcome f (if hd.Accepts d o.tag then _ else _)
      split <;> rfl
  | _ => rfl

variable {src : Program O A (fun _ => k) r} {dst : Program O B (fun _ => k) r}
    {f : A → Option B} {d : Dialect O V S}

private theorem step_eq
    (blocks : ∀ a b, f a = some b → block f (src.blocks a) = block some (dst.blocks b))
    {x : State V S A (fun _ => k) r} {y : State V S B (fun _ => k) r}
    (h : state f x = state some y) :
    outcome f (src.step d x) = outcome some (dst.step d y) := by
  rcases x with ⟨⟨a,u,m⟩,st⟩
  rcases y with ⟨⟨b,v,n⟩,tt⟩
  simp only [state, location, State.mk.injEq, Location.mk.injEq] at h
  obtain ⟨⟨hl, rfl, rfl⟩, hs⟩ := h
  simp only [Program.step, Program.runBlock, ← next_transfer, ← eval_block, blocks a b hl, hs]

theorem exec (blocks : ∀ a b, f a = some b →
      block f (src.blocks a) = block some (dst.blocks b))
    {x : State V S A (fun _ => k) r} {o : Output V S r} (h : src.Exec d x o)
    {y : State V S B (fun _ => k) r} (hm : state f x = state some y) : dst.Exec d y o := by
  induction h generalizing y with
  | done h =>
    have eq := step_eq (d := d) blocks hm
    rw [h] at eq
    cases e : dst.step d y <;> rw [e] at eq <;> cases eq
    exact .done e
  | next h _ ih =>
    have eq := step_eq (d := d) blocks hm
    rw [h] at eq
    cases e : dst.step d y <;> rw [e] at eq
    case next => exact .next e (ih (Outcome.next.inj eq))
    all_goals cases eq

end K256.Proofs.Generate.Serialize.Relabel
