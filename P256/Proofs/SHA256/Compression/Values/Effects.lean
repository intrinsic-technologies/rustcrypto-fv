import P256.Proofs.SHA256.Compression.Values.ValueRefinement

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

def Op.writes (operation : Op) (context : ValueContext) (values : Values) : List Write :=
  match operation with
  | .store32 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), (values.regs src).setWidth 32⟩]
  | .store64 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), values.regs src⟩]
  | .addStack32 off src =>
    [⟨.mem (context.stackPointer + BitVec.ofNat 64 off), values.stack off + (values.regs src).setWidth 32⟩]
  | .mov32 dst _ | .mov64 dst _ | .binary32 _ dst _ | .not32 dst |
    .rol32 dst _ | .shr32 dst _ | .lea32 dst _ _ _ _ | .bswap32 dst =>
    [⟨.reg dst, (operation.eval context values).regs dst⟩]

def Op.StoreValid : Op → Prop
  | .store32 off _ | .addStack32 off _ => off % 4 = 0 ∧ off + 4 ≤ 288
  | .store64 off _ => off % 4 = 0 ∧ off + 8 ≤ 288
  | _ => True

instance (operation : Op) : Decidable operation.StoreValid := by
  cases operation <;> unfold Op.StoreValid <;> infer_instance

theorem Op.eval_represents_after (operation : Op) (context : ValueContext)
    (values : Values) (model : RamState) (h : Represents context values model)
    (valid : operation.StoreValid)
    (separate : RangeApart context.stackPointer 288 context.inputPointer 64) :
    Represents context (operation.eval context values)
      (applyWrites model (operation.writes context values)) := by
  cases operation with
  | store32 off src => exact h.write32 off _ valid.1 valid.2 separate
  | store64 off src => exact h.write64 off _ valid.1 valid.2 separate
  | addStack32 off src => exact h.write32 off _ valid.1 valid.2 separate
  | mov32 dst src =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst ((src.read32 context values).setWidth 64)
  | mov64 dst src =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst (src.read64 context values)
  | binary32 operation dst src =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst ((operation.apply ((values.regs dst).setWidth 32)
        (src.read32 context values)).setWidth 64)
  | not32 dst =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst ((~~~((values.regs dst).setWidth 32)).setWidth 64)
  | rol32 dst count =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst (((values.regs dst).setWidth 32).rotateLeft count |>.setWidth 64)
  | shr32 dst count =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst ((((values.regs dst).setWidth 32) >>> count).setWidth 64)
  | lea32 dst base index scale disp =>
    cases index <;>
      simp only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk]
    all_goals exact h.writeReg dst _
  | bswap32 dst =>
    simpa only [Op.eval, Op.writes, writeReg, ↓reduceIte, applyWrites_cons, applyWrites_nil, Write.apply_mk] using
      h.writeReg dst ((P256.Proofs.Common.SHA256.Compression.bswap32 ((values.regs dst).setWidth 32)).setWidth 64)

end P256.Proofs.SHA256.Compression.Values
