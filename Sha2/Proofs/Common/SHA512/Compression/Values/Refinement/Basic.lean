import Sha2.Proofs.Common.SHA512.Compression.Values.Effects
import Sha2.Proofs.Common.SHA512.Compression.Safety.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

def source64 (context : ValueContext) (model : RamState) : Source → BitVec 64
  | .reg r => (Operand.reg r : Operand 64).read model
  | .imm value => value
  | .mem address => memLoad model.external (address.value context) 64

def ReadValid : Op → Prop
  | .mov64 _ src | .binary64 _ _ src => src.Valid 8
  | .addStack64 off _ | .xorStack64 off _ => (Address.stack off).Valid 8
  | _ => True

instance (address : Address) (bytes : Nat) : Decidable (address.Valid bytes) := by
  cases address <;> unfold Address.Valid <;> infer_instance

instance (source : Source) (bytes : Nat) : Decidable (source.Valid bytes) := by
  cases source <;> unfold Source.Valid <;> infer_instance

instance (operation : Op) : Decidable (ReadValid operation) := by
  cases operation <;> unfold ReadValid <;> infer_instance

def writes (context : ValueContext) (model : RamState) : Op → List Write
  | .mov64 dst src => [⟨.reg dst, source64 context model src⟩]
  | .store64 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      (Operand.reg src : Operand 64).read model⟩]
  | .addStack64 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 64 +
      (Operand.reg src : Operand 64).read model⟩]
  | .xorStack64 off src => [⟨.mem (context.stackPointer + BitVec.ofNat 64 off),
      memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 64 ^^^
      (Operand.reg src : Operand 64).read model⟩]
  | .binary64 op dst src => [⟨.reg dst,
      op.apply ((Operand.reg dst : Operand 64).read model) (source64 context model src)⟩]
  | .not64 dst => [⟨.reg dst, ~~~((Operand.reg dst : Operand 64).read model)⟩]
  | .rol64 dst count => [⟨.reg dst,
      ((Operand.reg dst : Operand 64).read model).rotateLeft count⟩]
  | .ror64 dst count => [⟨.reg dst,
      ((Operand.reg dst : Operand 64).read model).rotateRight count⟩]
  | .shr64 dst count => [⟨.reg dst,
      ((Operand.reg dst : Operand 64).read model) >>> count⟩]
  | .lea64 dst base index scale disp =>
      let indexed := match index with
        | none => 0
        | some r => (Operand.reg r : Operand 64).read model <<< scale
      [⟨.reg dst, (Operand.reg base : Operand 64).read model + indexed + disp⟩]
  | .bswap64 dst => [⟨.reg dst,
      Instructions.bswap64 ((Operand.reg dst : Operand 64).read model)⟩]

theorem writes_eq {context : ValueContext} {values : Values} {model : RamState}
    (rep : Represents context values model) (operation : Op) (valid : ReadValid operation) :
    operation.writes context values = writes context model operation := by
  cases operation with
  | mov64 dst src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes]
    rw [rep.source_read64 src valid]
    cases src <;> rfl
  | binary64 op dst src =>
    simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes]
    rw [rep.source_read64 src valid, rep.regs dst]
    cases src <;> rfl
  | addStack64 off src =>
    simp only [Op.writes, writes, rep.stack off valid.1 valid.2, rep.regs src]
  | xorStack64 off src =>
    simp only [Op.writes, writes, rep.stack off valid.1 valid.2, rep.regs src]
  | lea64 dst base index scale disp =>
    cases index <;> simp only [Op.writes, Op.eval, writeReg, ↓reduceIte, writes, rep.regs]
  | store64 off src | not64 src | rol64 src count | ror64 src count | shr64 src count | bswap64 src =>
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

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
