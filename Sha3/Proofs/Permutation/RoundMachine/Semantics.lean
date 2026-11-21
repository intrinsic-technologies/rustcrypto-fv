import Sha3.Proofs.Permutation.RoundMachine.Relation
import Sha3.Proofs.Permutation.LoadStore.Memory

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program

def destination : Instruction → Location
  | .mov dst _ | .xor dst _ | .and dst _ | .not dst | .rol dst _ | .xorConstant dst => dst

def value (rc : BitVec 64) (a : RoundAlgebra.State) : Instruction → BitVec 64
  | .mov _ src => read a src
  | .xor dst src => read a dst ^^^ read a src
  | .and dst src => read a dst &&& read a src
  | .not dst => ~~~ read a dst
  | .rol dst n => (read a dst).rotateLeft n
  | .xorConstant dst => read a dst ^^^ rc

def ValidWrite (dst : Location) : Prop :=
  ValidLocation dst ∧ dst ≠ .reg 4 ∧ dst ≠ .stack 160 ∧
    (match dst with | .reg _ => True | .stack offset => offset < 216)

def ValidInstruction (op : Instruction) : Prop :=
  ValidWrite (destination op) ∧
    match op with
    | .mov _ src | .xor _ src | .and _ src => ValidLocation src
    | _ => True

instance (dst : Location) : Decidable (ValidWrite dst) := by
  cases dst <;> unfold ValidWrite <;> infer_instance

instance (op : Instruction) : Decidable (ValidInstruction op) := by
  cases op <;> unfold ValidInstruction <;> infer_instance

def instructionEffect (sp next rc : BitVec 64) (op : Instruction)
    (flags : Option StatusFlagsOutcome) (s : RamState) : Effect :=
  writeEffect sp next (destination op) (value rc (model sp s) op) flags

theorem execute_eq_write (rc : BitVec 64) (a : RoundAlgebra.State) (op : Instruction) :
    execute rc a op = write a (destination op) (value rc a op) := by
  cases op <;> rfl

theorem models_value {sp rc : BitVec 64} {a : RoundAlgebra.State} {s : RamState}
    {op : Instruction} (h : Models sp a s) (hv : ValidInstruction op) :
    value rc (model sp s) op = value rc a op := by
  have hr (loc : Location) (hl : ValidLocation loc) :
      RoundAlgebra.read (model sp s) loc = RoundAlgebra.read a loc := by
    rw [← h loc hl]
    cases loc <;> rfl
  cases op <;> simp_all [value, ValidInstruction, ValidWrite, destination]

theorem models_execute {sp next rc : BitVec 64} {a : RoundAlgebra.State} {s t : RamState}
    {op : Instruction} {flags : Option StatusFlagsOutcome}
    (h : Models sp a s) (hv : ValidInstruction op)
    (he : (instructionEffect sp next rc op flags s).Holds s t) :
    Models sp (execute rc a op) t := by
  rw [execute_eq_write]
  unfold instructionEffect at he
  rw [models_value h hv] at he
  exact models_writeEffect h hv.1.1 he

structure RoundMemory (sp : BitVec 64) (s : RamState) : Prop where
  readable : MemReadable s sp 216
  tables : ∀ i, i < 216 → ¬ InPageTables (sp + BitVec.ofNat 64 i)
  program : ∀ i, i < 216 → ¬ InProgram (sp + BitVec.ofNat 64 i)

def constantOperand (copy : Copy) (s : RamState) : Operand 64 :=
  .mem ((Operand.reg 2 : Operand 64).read s + constantBase copy)

def ConstantPre (copy : Copy) (rc : BitVec 64) (op : Instruction) (s : RamState) : Prop :=
  match op with
  | .xorConstant _ =>
    MemReadable s ((Operand.reg 2 : Operand 64).read s + constantBase copy) 8 ∧
      (constantOperand copy s).read s = rc
  | _ => True

structure DataPre (copy : Copy) (sp rc : BitVec 64) (pc : Nat) (op : Instruction) (s : RamState) : Prop where
  rip : s.RIP = BitVec.ofNat 64 pc
  stack : (Operand.reg 4 : Operand 64).read s = sp
  memory : RoundMemory sp s
  constant : ConstantPre copy rc op s

def DataStep [Bindings] (copy : Copy) (pc next : Nat) (op : Instruction) (bytes : List UInt8) : Prop :=
  ∀ sp rc s, ReadyToStep s → CodeIn (codeRange (BitVec.ofNat 64 pc) bytes) s →
    DataPre copy sp rc pc op s → ∃ t flags,
      Machine.step s = some (.next t) ∧ ReadyToStep t ∧
        (instructionEffect sp (BitVec.ofNat 64 next) rc op flags s).Holds s t

end Sha3.Proofs.Permutation.RoundMachine
