import AesGcm.Proofs.Copied.X86Proofs.Refine.Store
import AesGcm.Proofs.Copied.X86Proofs.Refine.LayoutAttr

namespace X86Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift Prelude

inductive Atom where
  | reg (r : Fin Reg.count) (v : Value)
  | low (r : Fin Reg.count) (width : Nat) (v : BitVec width)
  | mem (address : BitVec 64) (width : Nat) (value : BitVec width)
  | words (address : BitVec 64) (width : Nat) {n : Nat} (values : Vector (BitVec width) n)
  | readable (address : BitVec 64) (length : Nat)
  | writable (address : BitVec 64) (length : Nat)
  | fact (p : Prop)

abbrev Atom.gpr (r : Fin Reg.count) (v : BitVec 64) : Atom := .reg r ⟨64, v⟩

def Atom.Holds (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) : Atom → Prop
  | .reg r v => args[r] = v
  | .low r w v => args[r].get w = v
  | .mem a w v => memLoad mem a w = v
  | .words a w vs => WordsAt mem a w vs
  | .readable a len => Readable mem a len
  | .writable a len => Writable code mem a len
  | .fact p => p

def Atom.All (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) : List Atom → Prop
  | [] => True
  | a :: as => a.Holds code args mem ∧ Atom.All code args mem as

structure Layout {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat}
    {results : Nat} (P : Program UOp ULabel usig results) (D : Dialect UOp UValue UStore)
    (lifted : Lifted) (Ctx : Type) where

  start : ULabel → lifted.Label

  Params : ULabel → Type

  args : (l : ULabel) → Params l → Values UValue (usig l)

  store : (l : ULabel) → Params l → UStore

  atoms : (l : ULabel) → Ctx → Params l → List Atom

  Result : Type

  output : Result → Output UValue UStore results

  done : Ctx → Result → List Atom

  retAddr : Ctx → BitVec 64

  original : Ctx → Ram

  regions : Ctx → List MemoryRegion

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}

structure Layout.Rel (L : Layout P D lifted Ctx) (code : CodeMap) (c : Ctx)
    (u : Location UValue UStore ULabel usig) (l : lifted.Location) : Prop where
  label : l.label = L.start u.label
  params : ∃ p, u.arguments = L.args u.label p ∧ u.store = L.store u.label p ∧
    Atom.All code l.arguments l.store (L.atoms u.label c p)
  frame : RamWriteFrame (L.original c) l.store (L.regions c)

structure Layout.RetRel (L : Layout P D lifted Ctx) (code : CodeMap) (c : Ctx)
    (uo : Output UValue UStore results) (lo : Output Value Ram Reg.count) : Prop where
  tag : lo.tag = some ⟨64, L.retAddr c⟩
  result : ∃ r, uo = L.output r ∧ Atom.All code lo.values lo.store (L.done c r)
  frame : RamWriteFrame (L.original c) lo.store (L.regions c)

def Layout.Resumes (L : Layout P D lifted Ctx) (code : CodeMap) (c' c : Ctx)
    (uf : CFG.StackFrame UValue ULabel usig results) (lf : lifted.StackFrame) : Prop :=
  ∀ uo lo, L.RetRel code c' uo lo → uf.Accepts D uo.tag = true →
    lf.Accepts (dialect code) lo.tag = true ∧ L.Rel code c (uf.resume uo) (lf.resume lo)

def Layout.StackRel (L : Layout P D lifted Ctx) (code : CodeMap) (c₀ : Ctx) :
    Ctx → List (CFG.StackFrame UValue ULabel usig results) → List lifted.StackFrame → Prop
  | c, [], [] => c = c₀
  | c, uf :: us, lf :: ls => ∃ c', L.Resumes code c c' uf lf ∧ L.StackRel code c₀ c' us ls
  | _, _, _ => False

def Layout.StateRel (L : Layout P D lifted Ctx) (code : CodeMap) (c₀ : Ctx)
    (u : CFG.State UValue UStore ULabel usig results) (l : lifted.State) : Prop :=
  ∃ c, L.Rel code c u.location l.location ∧ L.StackRel code c₀ c u.stack l.stack

inductive JumpRun (lifted : Lifted) (code : CodeMap) :
    lifted.Location → lifted.Location → Prop where
  | refl (l : lifted.Location) : JumpRun lifted code l l
  | jump {l l' l'' : lifted.Location} : lifted.program.runBlock (dialect code) l = .jump l' →
      JumpRun lifted code l' l'' → JumpRun lifted code l l''

def Ahead (lifted : Lifted) (code : CodeMap) (E : lifted.Location → Prop) (l : lifted.Location) :
    Prop :=
  ∃ l', JumpRun lifted code l l' ∧ E l'

def Onward (lifted : Lifted) (code : CodeMap) (E : lifted.Location → Prop)
    (fin : Transfer Value Ram lifted.Label signature Reg.count → Prop) :
    Transfer Value Ram lifted.Label signature Reg.count → Prop
  | .jump l => Ahead lifted code E l
  | t => fin t

def CallTo {lifted : Lifted} (Q : lifted.Location → lifted.StackFrame → Prop) :
    Transfer Value Ram lifted.Label signature Reg.count → Prop
  | .call l fr => Q l fr
  | _ => False

def ReturnOf {lifted : Lifted} (Q : Output Value Ram Reg.count → Prop) :
    Transfer Value Ram lifted.Label signature Reg.count → Prop
  | .returned o => Q o
  | _ => False

def Layout.MatchedBy (L : Layout P D lifted Ctx) (code : CodeMap) (c : Ctx) (l : lifted.Location) :
    Transfer UValue UStore ULabel usig results → Prop
  | .jump u => Ahead lifted code (L.Rel code c u) l
  | .call u uf => Ahead lifted code (fun l' => CallTo (fun l'' lf =>
      ∃ c', L.Rel code c' u l'' ∧ L.Resumes code c' c uf lf)
        (lifted.program.runBlock (dialect code) l')) l
  | .returned uo => Ahead lifted code (fun l' =>
      ReturnOf (L.RetRel code c uo) (lifted.program.runBlock (dialect code) l')) l
  | .stuck => True

def Layout.BlockSimulation (L : Layout P D lifted Ctx) (code : CodeMap) (label : ULabel) : Prop :=
  ∀ (c : Ctx) (arguments : Values UValue (usig label)) (store : UStore) (l : lifted.Location),
    L.Rel code c ⟨label, arguments, store⟩ l →
      L.MatchedBy code c l (P.runBlock D ⟨label, arguments, store⟩)

end X86Proofs.Refine
