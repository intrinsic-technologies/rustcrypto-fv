import Hkdf.Proofs.Common.SHA256.Compression.Values.Simulation

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

def source32 (context : ValueContext) (model : RamState) : Source → BitVec 32
  | .reg r => (Operand.reg r : Operand 32).read model
  | .imm value => value
  | .mem address => memLoad model.external (address.value context) 32

def source64 (context : ValueContext) (model : RamState) : Source → BitVec 64
  | .reg r => (Operand.reg r : Operand 64).read model
  | .imm value => value.setWidth 64
  | .mem address => memLoad model.external (address.value context) 64

def ReadValid : Op → Prop
  | .mov32 _ src | .binary32 _ _ src => src.Valid 4
  | .mov64 _ src => src.Valid 8
  | .addStack32 off _ => (Address.stack off).Valid 4
  | _ => True

instance (address : Address) (bytes : Nat) : Decidable (address.Valid bytes) := by
  cases address <;> unfold Address.Valid <;> infer_instance

instance (source : Source) (bytes : Nat) : Decidable (source.Valid bytes) := by
  cases source <;> unfold Source.Valid <;> infer_instance

instance (operation : Op) : Decidable (ReadValid operation) := by
  cases operation <;> unfold ReadValid <;> infer_instance

def writes (context : ValueContext) (model : RamState) : Op → List Write
  | .mov32 dst src => [⟨.reg dst, (source32 context model src).setWidth 64⟩]
  | .mov64 dst src => [⟨.reg dst, source64 context model src⟩]
  | .store32 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      (Operand.reg src : Operand 32).read model⟩]
  | .store64 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      (Operand.reg src : Operand 64).read model⟩]
  | .addStack32 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 32 +
      (Operand.reg src : Operand 32).read model⟩]
  | .binary32 op dst src => [⟨.reg dst,
      (op.apply ((Operand.reg dst : Operand 32).read model) (source32 context model src)).setWidth 64⟩]
  | .not32 dst => [⟨.reg dst, (~~~((Operand.reg dst : Operand 32).read model)).setWidth 64⟩]
  | .rol32 dst count => [⟨.reg dst,
      (((Operand.reg dst : Operand 32).read model).rotateLeft count).setWidth 64⟩]
  | .shr32 dst count => [⟨.reg dst,
      (((Operand.reg dst : Operand 32).read model) >>> count).setWidth 64⟩]
  | .lea32 dst base index scale disp =>
      let indexed := match index with
        | none => 0
        | some r => (Operand.reg r : Operand 64).read model <<< scale
      [⟨.reg dst, ((((Operand.reg base : Operand 64).read model + indexed + disp).setWidth 32).setWidth 64)⟩]
  | .bswap32 dst => [⟨.reg dst,
      (Compression.bswap32 ((Operand.reg dst : Operand 32).read model)).setWidth 64⟩]

theorem writes_eq {context : ValueContext} {values : Values} {model : RamState}
    (rep : Represents context values model) (operation : Op) (valid : ReadValid operation) :
    operation.writes context values = writes context model operation := by
  cases operation with
  | mov32 dst src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes]
    rw [rep.source_read32 src valid]
    cases src <;> rfl
  | mov64 dst src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes]
    rw [rep.source_read64 src valid]
    cases src <;> rfl
  | binary32 op dst src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes]
    rw [rep.source_read32 src valid, rep.regs dst]
    cases src <;> rfl
  | addStack32 off src =>
    simp only [Op.writes, writes, rep.stack off valid.1 valid.2, rep.regs src]
    rfl
  | lea32 dst base index scale disp =>
    cases index <;> simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes, rep.regs]
  | store32 off src | store64 off src | not32 src | rol32 src count | shr32 src count | bswap32 src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes, rep.regs]
    all_goals rfl

variable [Bindings]

theorem step {initial : RamState} {instruction : CheckedInstruction}
    {operation : Op} {position : Safety.Position}
    (storeValid : operation.StoreValid) (readValid : ReadValid operation)
    (effect : ∀ model, Safety.State initial model position →
      (instruction.effect model).writes = writes (contextOfRam initial) model operation) :
    StepRefinement initial instruction operation position := by
  refine ⟨storeValid, fun model values state rep => ?_⟩
  exact (effect model state).trans (writes_eq rep operation readValid).symm

end Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement
