namespace P256.Proofs.CFG

scoped macro:max "%" n:num : term => `(Fin.mk $n (by first | decide | omega))

abbrev Values (Value : Type) (n : Nat) := Vector Value n

structure Edge (Label : Type) (signature : Label → Nat) (n : Nat) where
  target : Label
  arguments : Vector (Fin n) (signature target)

structure Cont (Label : Type) (signature : Label → Nat) (results n : Nat) where
  {size : Nat}
  target : Label
  kept : Vector (Fin n) size
  arity : results + size = signature target := by decide
  guard : Option (Fin n) := none

inductive Terminator (Label : Type) (signature : Label → Nat) (results n : Nat) where

  | br (edge : Edge Label signature n)

  | condBr (condition : Fin n) (onTrue onFalse : Edge Label signature n)

  | call (callee : Edge Label signature n) (cont : Cont Label signature results n)

  | ret (values : Vector (Fin n) results) (tag : Option (Fin n) := none)

inductive Block (Op : Nat → Type) (Label : Type) (signature : Label → Nat) (results : Nat) :
    Nat → Type where

  | letOp {n arity : Nat} (op : Op arity) (operands : Vector (Fin n) arity)
      (next : Block Op Label signature results (n + 1)) : Block Op Label signature results n

  | terminate {n : Nat} (terminator : Terminator Label signature results n) :
      Block Op Label signature results n

structure Dialect (Op : Nat → Type) (Value Store : Type) where
  eval : {arity : Nat} → Op arity → Values Value arity → Store → Option (Value × Store)
  truth : Value → Bool

  accepts : Value → Value → Bool := fun _ _ => true

def Dialect.pureOp {Value Store : Type} {arity : Nat} (f : Values Value arity → Value) :
    Values Value arity → Store → Option (Value × Store) :=
  fun args store => some (f args, store)

def Dialect.ofPure {Op : Nat → Type} {Value Store : Type}
    (eval : {arity : Nat} → Op arity → Values Value arity → Value) (truth : Value → Bool) :
    Dialect Op Value Store where
  eval op := Dialect.pureOp (eval op)
  truth := truth

structure Location (Value Store Label : Type) (signature : Label → Nat) where
  label : Label
  arguments : Values Value (signature label)
  store : Store

structure Output (Value Store : Type) (results : Nat) where
  values : Values Value results
  tag : Option Value := none
  store : Store

structure StackFrame (Value Label : Type) (signature : Label → Nat) (results : Nat) where
  {size : Nat}
  target : Label
  kept : Values Value size
  arity : results + size = signature target
  guard : Option Value

structure State (Value Store Label : Type) (signature : Label → Nat) (results : Nat) where
  location : Location Value Store Label signature
  stack : List (StackFrame Value Label signature results) := []

inductive Transfer (Value Store Label : Type) (signature : Label → Nat) (results : Nat) where
  | jump (location : Location Value Store Label signature)
  | call (location : Location Value Store Label signature)
      (frame : StackFrame Value Label signature results)
  | returned (output : Output Value Store results)
  | stuck

inductive Outcome (Value Store Label : Type) (signature : Label → Nat) (results : Nat) where
  | next (state : State Value Store Label signature results)
  | done (output : Output Value Store results)
  | stuck

structure Program (Op : Nat → Type) (Label : Type) (signature : Label → Nat) (results : Nat) where
  blocks : (label : Label) → Block Op Label signature results (signature label)

section Semantics

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}

def Values.select {n arity : Nat} (scope : Values Value n)
    (operands : Vector (Fin n) arity) : Values Value arity :=
  ⟨(operands.toList.map fun i => scope[i]).toArray, by simp⟩

def Edge.eval {n : Nat} (edge : Edge Label signature n) (scope : Values Value n)
    (store : Store) : Location Value Store Label signature :=
  ⟨edge.target, scope.select edge.arguments, store⟩

def Cont.eval {n : Nat} (cont : Cont Label signature results n) (scope : Values Value n) :
    StackFrame Value Label signature results :=
  ⟨cont.target, scope.select cont.kept, cont.arity, cont.guard.map (scope[·])⟩

def Terminator.eval {n : Nat} (dialect : Dialect Op Value Store)
    (terminator : Terminator Label signature results n) (scope : Values Value n)
    (store : Store) : Transfer Value Store Label signature results :=
  match terminator with
  | .br edge => .jump (edge.eval scope store)
  | .condBr condition onTrue onFalse =>
      if dialect.truth scope[condition] then .jump (onTrue.eval scope store)
      else .jump (onFalse.eval scope store)
  | .call callee cont => .call (callee.eval scope store) (cont.eval scope)
  | .ret returned tag => .returned ⟨scope.select returned, tag.map (scope[·]), store⟩

def Block.eval (dialect : Dialect Op Value Store) {n : Nat} :
    Block Op Label signature results n → Values Value n → Store →
      Transfer Value Store Label signature results
  | .letOp op operands next, scope, store =>
      match dialect.eval op (scope.select operands) store with
      | some (value, store') => next.eval dialect (scope.push value) store'
      | none => .stuck
  | .terminate terminator, scope, store => terminator.eval dialect scope store

def Program.runBlock (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) (location : Location Value Store Label signature) :
    Transfer Value Store Label signature results :=
  (program.blocks location.label).eval dialect location.arguments location.store

def StackFrame.Accepts (dialect : Dialect Op Value Store)
    (frame : StackFrame Value Label signature results) (tag : Option Value) : Bool :=
  match frame.guard, tag with
  | none, _ => true
  | some guard, some tag => dialect.accepts guard tag
  | some _, none => false

def StackFrame.resume (frame : StackFrame Value Label signature results)
    (output : Output Value Store results) : Location Value Store Label signature :=
  ⟨frame.target, (output.values ++ frame.kept).cast frame.arity, output.store⟩

def Transfer.next (dialect : Dialect Op Value Store)
    (stack : List (StackFrame Value Label signature results)) :
    Transfer Value Store Label signature results → Outcome Value Store Label signature results
  | .jump location => .next ⟨location, stack⟩
  | .call location frame => .next ⟨location, frame :: stack⟩
  | .returned output =>
      match stack with
      | [] => .done output
      | frame :: rest =>
          if frame.Accepts dialect output.tag then .next ⟨frame.resume output, rest⟩ else .stuck
  | .stuck => .stuck

def Program.step (program : Program Op Label signature results) (dialect : Dialect Op Value Store)
    (state : State Value Store Label signature results) :
    Outcome Value Store Label signature results :=
  (program.runBlock dialect state.location).next dialect state.stack

def Program.run (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) :
    Nat → State Value Store Label signature results → Option (Output Value Store results)
  | 0, _ => none
  | fuel + 1, state =>
      match program.step dialect state with
      | .done output => some output
      | .next state' => program.run dialect fuel state'
      | .stuck => none

inductive Program.Exec (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) :
    State Value Store Label signature results → Output Value Store results → Prop where

  | done {state output} (h : program.step dialect state = .done output) :
      program.Exec dialect state output

  | next {state next output} (h : program.step dialect state = .next next)
      (tail : program.Exec dialect next output) : program.Exec dialect state output

end Semantics

end P256.Proofs.CFG
