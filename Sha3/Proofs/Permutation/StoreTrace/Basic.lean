import Sha3.Proofs.Permutation.LoadStore.Store.Basic
import Sha3.Proofs.Permutation.LoadStore.Store.Normalize
import Sha3.Proofs.Permutation.RoundMachine.Relation

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

inductive Location where
  | reg (r : Fin 16)
  | stack (i : Fin 34)
  | output (i : Fin 25)
  deriving DecidableEq

def operand (sp pointer : BitVec 64) : Location → Operand 64
  | .reg r => .reg (BitVec.ofNat 5 r.val)
  | .stack i => .mem (sp + BitVec.ofNat 64 (8 * i.val))
  | .output i => .mem (pointer + BitVec.ofNat 64 (8 * i.val))

abbrev State := Location → BitVec 64

def model (sp pointer : BitVec 64) (s : RamState) : State :=
  fun loc ↦ (operand sp pointer loc).read s

def Models (sp pointer : BitVec 64) (a : State) (s : RamState) : Prop :=
  ∀ loc, (operand sp pointer loc).read s = a loc

structure Move where
  dst : Location
  src : Location
  deriving DecidableEq

def execute (a : State) (op : Move) : State :=
  fun loc ↦ if loc = op.dst then a op.src else a loc

def AllowedWrite : Location → Prop
  | .reg r => r ∈ ([0, 2, 6] : List (Fin 16))
  | .stack _ => False
  | .output _ => True

instance (loc : Location) : Decidable (AllowedWrite loc) := by
  cases loc <;> unfold AllowedWrite <;> infer_instance

def moveEffect (sp pointer next : BitVec 64) (op : Move) (s : RamState) : Effect where
  rip := next
  writes := [⟨operand sp pointer op.dst, (operand sp pointer op.src).read s⟩]

structure Memory (copy : Copy) (sp pointer : BitVec 64) (s : RamState) : Prop where
  frameRead : MemReadable s sp 272
  outputRead : MemReadable s pointer 200
  apart : RangeApart pointer 200 sp 272
  codeApart : RangeApart pointer 200 (storeAddress copy) Store.bytes.length
  tables : ∀ i, i < 200 → ¬ InPageTables (pointer + BitVec.ofNat 64 i)

def PointerPre (pointer : BitVec 64) (op : Move) (s : RamState) : Prop :=
  match op.dst with
  | .output _ => (Operand.reg 2 : Operand 64).read s = pointer
  | _ => True

structure StepPre (copy : Copy) (sp pointer pc : BitVec 64) (op : Move) (s : RamState) : Prop where
  rip : s.RIP = pc
  stack : (Operand.reg 4 : Operand 64).read s = sp
  pointerValue : PointerPre pointer op s
  memory : Memory copy sp pointer s

def TraceStep [Bindings] (copy : Copy) (pc next : BitVec 64)
    (op : Move) (bytes : List UInt8) : Prop :=
  ∀ sp pointer s, ReadyToStep s → CodeIn (codeRange pc bytes) s →
    StepPre copy sp pointer pc op s → ∃ t,
      Machine.step s = some (.next t) ∧ ReadyToStep t ∧
        (moveEffect sp pointer next op s).Holds s t

end Sha3.Proofs.Permutation.StoreTrace
