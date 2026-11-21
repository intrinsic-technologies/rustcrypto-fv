import AesGcm.Proofs.Copied.X86Proofs.CFG.IR

namespace X86Proofs.CFG

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}

@[simp] theorem Values.getElem_select {n arity : Nat} (scope : Values Value n)
    (operands : Vector (Fin n) arity) (i : Nat) (h : i < arity) :
    (scope.select operands)[i] = scope[operands[i]] := by
  simp [Values.select, Vector.getElem_mk, Vector.getElem_toList]

theorem Values.select_eq_map {n arity : Nat} (scope : Values Value n)
    (operands : Vector (Fin n) arity) : scope.select operands = operands.map (scope[·]) :=
  Vector.ext fun i h => by simp

theorem Values.toList_select {n arity : Nat} (scope : Values Value n)
    (operands : Vector (Fin n) arity) :
    (scope.select operands).toList = operands.toList.map (scope[·]) := by
  simp [Values.select]

section Next

variable {dialect : Dialect Op Value Store}
  {stack : List (StackFrame Value Label signature results)}

@[simp] theorem Transfer.next_jump (location : Location Value Store Label signature) :
    (Transfer.jump location : Transfer Value Store Label signature results).next dialect stack =
      .next ⟨location, stack⟩ := rfl

@[simp] theorem Transfer.next_call (location : Location Value Store Label signature)
    (frame : StackFrame Value Label signature results) :
    (Transfer.call location frame).next dialect stack = .next ⟨location, frame :: stack⟩ := rfl

@[simp] theorem Transfer.next_returned_nil (output : Output Value Store results) :
    (Transfer.returned output : Transfer Value Store Label signature results).next dialect [] =
      .done output := rfl

theorem Transfer.next_returned_cons (output : Output Value Store results)
    (frame : StackFrame Value Label signature results) :
    (Transfer.returned output).next dialect (frame :: stack) =
      if frame.Accepts dialect output.tag then .next ⟨frame.resume output, stack⟩ else .stuck :=
  rfl

@[simp] theorem Transfer.next_stuck :
    (Transfer.stuck : Transfer Value Store Label signature results).next dialect stack = .stuck :=
  rfl

theorem Transfer.next_ite {c : Prop} [Decidable c] (a b : Transfer Value Store Label signature results) :
    (if c then a else b).next dialect stack = if c then a.next dialect stack else b.next dialect stack :=
  apply_ite _ c a b

theorem Transfer.next_ne_stuck {t : Transfer Value Store Label signature results}
    (h : t.next dialect stack ≠ .stuck) : t ≠ .stuck := by
  rintro rfl
  exact h rfl

end Next

theorem Block.eval_letOp_some {dialect : Dialect Op Value Store} {n arity : Nat} {op : Op arity}
    {operands : Vector (Fin n) arity} {next : Block Op Label signature results (n + 1)}
    {scope : Values Value n} {store : Store} {args : Values Value arity} {v : Value}
    {store' : Store} {t : Transfer Value Store Label signature results}
    (hargs : scope.select operands = args) (h : dialect.eval op args store = some (v, store'))
    (hnext : next.eval dialect (scope.push v) store' = t) :
    (Block.letOp op operands next).eval dialect scope store = t := by
  simp only [Block.eval, hargs, h, hnext]

theorem Block.eval_letOp_ite {dialect : Dialect Op Value Store} {n arity : Nat} {op : Op arity}
    {operands : Vector (Fin n) arity} {next : Block Op Label signature results (n + 1)}
    {scope : Values Value n} {store : Store} {args : Values Value arity} {c : Prop}
    [Decidable c] {v : Value} {store' : Store} {t : Transfer Value Store Label signature results}
    (hargs : scope.select operands = args)
    (h : dialect.eval op args store = if c then some (v, store') else none)
    (hnext : next.eval dialect (scope.push v) store' = t) :
    (Block.letOp op operands next).eval dialect scope store = if c then t else .stuck := by
  by_cases hc : c <;> simp [Block.eval, hargs, h, hnext, hc]

theorem Block.eval_letOp_ite_stuck {dialect : Dialect Op Value Store} {n arity : Nat}
    {op : Op arity} {operands : Vector (Fin n) arity}
    {next : Block Op Label signature results (n + 1)} {scope : Values Value n}
    {store : Store} {args : Values Value arity} {c : Prop} [Decidable c] {v : Value}
    {store' : Store} (hargs : scope.select operands = args)
    (h : dialect.eval op args store = if c then some (v, store') else none)
    (hnext : next.eval dialect (scope.push v) store' = .stuck) :
    (Block.letOp op operands next).eval dialect scope store = .stuck :=
  (Block.eval_letOp_ite hargs h hnext).trans (ite_self _)

theorem Block.eval_letOp_none {dialect : Dialect Op Value Store} {n arity : Nat} {op : Op arity}
    {operands : Vector (Fin n) arity} {next : Block Op Label signature results (n + 1)}
    {scope : Values Value n} {store : Store} {args : Values Value arity}
    (hargs : scope.select operands = args) (h : dialect.eval op args store = none) :
    (Block.letOp op operands next).eval dialect scope store = .stuck := by
  simp only [Block.eval, hargs, h]

def Values.Prefix {m n : Nat} (R : Values Value m) (R' : Values Value n) : Prop :=
  m ≤ n ∧ ∀ j (h : j < m) (h' : j < n), R'[j] = R[j]

theorem Values.Prefix.refl {n : Nat} (R : Values Value n) : R.Prefix R :=
  ⟨Nat.le_refl n, fun _ _ _ => rfl⟩

theorem Values.Prefix.push {m n : Nat} {R : Values Value m} {R' : Values Value n}
    (h : R.Prefix R') (v : Value) : R.Prefix (R'.push v) :=
  ⟨Nat.le_succ_of_le h.1, fun j hj _ => by
    rw [Vector.getElem_push_lt (Nat.lt_of_lt_of_le hj h.1)]
    exact h.2 j hj _⟩

theorem Values.Prefix.read {m n : Nat} {R : Values Value m} {R' : Values Value n}
    (h : R.Prefix R') {j : Nat} (hj : j < m) (hj' : j < n) {x : Value} (hx : R[j] = x) :
    R'[j] = x :=
  (h.2 j hj hj').trans hx

theorem Values.getElem_push_self {n : Nat} (R : Values Value n) (v : Value) :
    (R.push v)[n] = v :=
  Vector.getElem_push_last

theorem Values.getElem_push_of_lt {n : Nat} {R : Values Value n} {v x : Value} {j : Nat}
    (hj : j < n) (hx : R[j] = x) : (R.push v)[j] = x :=
  (Vector.getElem_push_lt hj).trans hx

theorem Values.select_eq {n m : Nat} {R : Values Value n} {operands : Vector (Fin n) m}
    {args : Values Value m} (h : operands.toList.map (fun i => R[i.val]) = args.toList) :
    R.select operands = args := by
  apply Vector.toList_inj.mp
  rw [Values.toList_select]
  exact h

section Terminators

variable {dialect : Dialect Op Value Store} {n : Nat} {R : Values Value n} {store : Store}

theorem Terminator.eval_br {target : Label} {arguments : Vector (Fin n) (signature target)}
    {a : Values Value (signature target)} (h : R.select arguments = a) :
    (Terminator.br ⟨target, arguments⟩ : Terminator Label signature results n).eval dialect R
      store = .jump ⟨target, a, store⟩ := by
  simp only [Terminator.eval, Edge.eval, h]

theorem Terminator.eval_condBr {c : Fin n} {t₁ t₂ : Label}
    {arguments₁ : Vector (Fin n) (signature t₁)} {arguments₂ : Vector (Fin n) (signature t₂)}
    {x : Value} {a₁ : Values Value (signature t₁)} {a₂ : Values Value (signature t₂)}
    (hc : R[c.val] = x) (h₁ : R.select arguments₁ = a₁) (h₂ : R.select arguments₂ = a₂) :
    (Terminator.condBr c ⟨t₁, arguments₁⟩ ⟨t₂, arguments₂⟩ :
        Terminator Label signature results n).eval dialect R store =
      if dialect.truth x then .jump ⟨t₁, a₁, store⟩ else .jump ⟨t₂, a₂, store⟩ := by
  simp only [Terminator.eval, Edge.eval, h₁, h₂, ← hc]
  rfl

theorem Terminator.eval_call {target : Label} {arguments : Vector (Fin n) (signature target)}
    {size : Nat} {resume : Label} {kept : Vector (Fin n) size}
    {arity : results + size = signature resume} {guard : Option (Fin n)}
    {a : Values Value (signature target)} {k : Values Value size} {g : Option Value}
    (arity' : results + size = signature resume) (h : R.select arguments = a)
    (hk : R.select kept = k) (hg : guard.map (fun i => R[i.val]) = g) :
    (Terminator.call ⟨target, arguments⟩ ⟨resume, kept, arity, guard⟩).eval dialect R store =
      .call ⟨target, a, store⟩ ⟨resume, k, arity', g⟩ := by
  simp only [Terminator.eval, Edge.eval, Cont.eval, h, hk, ← hg]
  rfl

theorem Terminator.eval_ret {values : Vector (Fin n) results} {tag : Option (Fin n)}
    {a : Values Value results} {g : Option Value} (h : R.select values = a)
    (hg : tag.map (fun i => R[i.val]) = g) :
    (Terminator.ret values tag : Terminator Label signature results n).eval dialect R store =
      .returned ⟨a, g, store⟩ := by
  simp only [Terminator.eval, h, ← hg]
  rfl

end Terminators

section Run

variable {program : Program Op Label signature results} {dialect : Dialect Op Value Store}
  {state : State Value Store Label signature results} {left right : Output Value Store results}

theorem Program.run_add {fuel : Nat} (h : program.run dialect fuel state = some left)
    (extra : Nat) : program.run dialect (fuel + extra) state = some left := by
  induction fuel generalizing state with
  | zero => simp [Program.run] at h
  | succ fuel ih =>
      cases hs : program.step dialect state with
      | done output => simpa [Program.run, hs, Nat.succ_add] using h
      | next next =>
          simp only [Program.run, hs] at h
          simpa [Program.run, hs, Nat.succ_add] using ih h
      | stuck => simp [Program.run, hs] at h

theorem Program.run_deterministic {m n : Nat} (hl : program.run dialect m state = some left)
    (hr : program.run dialect n state = some right) : left = right := by
  have hm := Program.run_add hl n
  have hn := Program.run_add hr m
  rw [Nat.add_comm n m, hm] at hn
  exact Option.some.inj hn

end Run

end X86Proofs.CFG
