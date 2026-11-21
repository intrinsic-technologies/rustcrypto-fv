import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
import Sha2.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field.Montgomery.Schoolbook

def Op.writes (operation : Op) (context : ValueContext) (values : Values) : List Write :=
  match operation with
  | .store64 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), values.regs src⟩]
  | .addStack64 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), values.stack off + values.regs src⟩]
  | .xorStack64 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), values.stack off ^^^ values.regs src⟩]
  | .mov64 dst _ | .binary64 _ dst _ | .not64 dst | .rol64 dst _ | .ror64 dst _ | .shr64 dst _ |
    .lea64 dst _ _ _ _ | .bswap64 dst =>
    [⟨.reg dst, (operation.eval context values).regs dst⟩]

def Op.StoreValid : Op → Prop
  | .store64 off _ | .addStack64 off _ | .xorStack64 off _ => off % 8 = 0 ∧ off + 8 ≤ 416
  | _ => True

instance (operation : Op) : Decidable operation.StoreValid := by
  cases operation <;> unfold Op.StoreValid <;> infer_instance

namespace Represents

variable {context : ValueContext} {values : Values} {model : RamState}

theorem write64 (h : Represents context values model) (off : Nat) (value : BitVec 64)
    (align : off % 8 = 0) (bound : off + 8 ≤ 416)
    (separateInput : RangeApart context.stackPointer 416 context.inputPointer 128)
    (separateConstants : RangeApart context.stackPointer 416 context.constantPointer 640) :
    Represents context (values.write64 off value)
      ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 64).write model value) := by
  refine ⟨h.regs, ?_, ?_, ?_⟩
  · intro index indexAlign indexBound
    change (if index = off then value else values.stack index) = _
    rw [show ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 64).write model value).external =
      memStore model.external (context.stackPointer + BitVec.ofNat 64 off) value from rfl]
    by_cases same : index = off
    · subst index
      simp only [ite_true]
      exact (memLoad_memStore_same model.external
        (context.stackPointer + BitVec.ofNat 64 off) value (by decide) (by decide)).symm
    · simp only [ite_eq_right same]
      have apart : RangeApart
          (context.stackPointer + BitVec.ofNat 64 off) 8
          (context.stackPointer + BitVec.ofNat 64 index) 8 := by
        apply RangeApart.offsets context.stackPointer (a := off) (b := index)
          (len := 8) (count := 8) (by omega) (by omega)
        omega
      calc
        values.stack index = memLoad model.external
            (context.stackPointer + BitVec.ofNat 64 index) 64 := h.stack index indexAlign indexBound
        _ = memLoad (memStore model.external
            (context.stackPointer + BitVec.ofNat 64 off) value)
            (context.stackPointer + BitVec.ofNat 64 index) 64 :=
          (memLoad_memStore_rangeApart model.external
            (context.stackPointer + BitVec.ofNat 64 off)
            (context.stackPointer + BitVec.ofNat 64 index) value 64 apart).symm
  · intro index indexAlign indexBound
    change _ = memLoad (memStore _ _ _) _ 64
    have apart : RangeApart
        (context.stackPointer + BitVec.ofNat 64 off) 8
        (context.inputPointer + BitVec.ofNat 64 index) 8 := by
      intro i hi j hj
      have hneq := separateInput (off + i) (by omega) (index + j) (by omega)
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using hneq
    calc
      context.inputWords index = memLoad model.external
          (context.inputPointer + BitVec.ofNat 64 index) 64 := h.input index indexAlign indexBound
      _ = memLoad (memStore model.external
          (context.stackPointer + BitVec.ofNat 64 off) value)
          (context.inputPointer + BitVec.ofNat 64 index) 64 :=
        (memLoad_memStore_rangeApart model.external
          (context.stackPointer + BitVec.ofNat 64 off)
          (context.inputPointer + BitVec.ofNat 64 index) value 64 apart).symm
  · intro index indexAlign indexBound
    change _ = memLoad (memStore _ _ _) _ 64
    have apart : RangeApart
        (context.stackPointer + BitVec.ofNat 64 off) 8
        (context.constantPointer + BitVec.ofNat 64 index) 8 := by
      intro i hi j hj
      have hneq := separateConstants (off + i) (by omega) (index + j) (by omega)
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using hneq
    calc
      context.constants index = memLoad model.external
          (context.constantPointer + BitVec.ofNat 64 index) 64 := h.constants index indexAlign indexBound
      _ = memLoad (memStore model.external
          (context.stackPointer + BitVec.ofNat 64 off) value)
          (context.constantPointer + BitVec.ofNat 64 index) 64 :=
        (memLoad_memStore_rangeApart model.external
          (context.stackPointer + BitVec.ofNat 64 off)
          (context.constantPointer + BitVec.ofNat 64 index) value 64 apart).symm

end Represents

theorem Op.eval_represents_after (operation : Op) (context : ValueContext)
    (values : Values) (model : RamState) (h : Represents context values model)
    (valid : operation.StoreValid)
    (separateInput : RangeApart context.stackPointer 416 context.inputPointer 128)
    (separateConstants : RangeApart context.stackPointer 416 context.constantPointer 640) :
    Represents context (operation.eval context values)
      (applyWrites model (operation.writes context values)) := by
  cases operation with
  | store64 off src => exact h.write64 off _ valid.1 valid.2 separateInput separateConstants
  | addStack64 off src => exact h.write64 off _ valid.1 valid.2 separateInput separateConstants
  | xorStack64 off src => exact h.write64 off _ valid.1 valid.2 separateInput separateConstants
  | mov64 dst src =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (src.read64 context values)
  | binary64 operation dst src =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (operation.apply (values.regs dst) (src.read64 context values))
  | not64 dst =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (~~~values.regs dst)
  | rol64 dst count =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (values.regs dst |>.rotateLeft count)
  | ror64 dst count =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (values.regs dst |>.rotateRight count)
  | shr64 dst count =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (values.regs dst >>> count)
  | lea64 dst base index scale disp =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst _
  | bswap64 dst =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil,
      Write.apply_mk] using h.writeReg dst (Instructions.bswap64 (values.regs dst))

end Sha2.Proofs.Common.SHA512.Compression.Values
