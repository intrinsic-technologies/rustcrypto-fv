import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Algebra

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values

open Correctness

theorem low_read64 (context : ValueContext) (state : Values) (address : Address) :
    (read64 context state address).setWidth 32 = read32 context state address := by
  cases address <;> exact low_append _ _

theorem Source.low_read64 (source : Source) (context : ValueContext) (state : Values) :
    (source.read64 context state).setWidth 32 = source.read32 context state := by
  cases source with
  | reg => rfl
  | imm value => exact low_extend value
  | mem address => exact Values.low_read64 context state address

theorem low_writeReg (state : Values) (dst r : BitVec 5) (value : BitVec 64) :
    ((state.writeReg dst value).regs r).setWidth 32 =
      if r = dst then value.setWidth 32 else (state.regs r).setWidth 32 := by
  simp only [writeReg]
  split <;> rfl

theorem Op.low_eval (operation : Op) (context : ValueContext) (state : Values) (r : BitVec 5) :
    ((operation.eval context state).regs r).setWidth 32 =
      match operation with
      | .mov32 dst src | .mov64 dst src =>
        if r = dst then src.read32 context state else (state.regs r).setWidth 32
      | .store32 _ _ | .store64 _ _ | .addStack32 _ _ => (state.regs r).setWidth 32
      | .binary32 op dst src =>
        if r = dst then op.apply ((state.regs dst).setWidth 32) (src.read32 context state)
        else (state.regs r).setWidth 32
      | .not32 dst =>
        if r = dst then ~~~((state.regs dst).setWidth 32) else (state.regs r).setWidth 32
      | .rol32 dst count =>
        if r = dst then ((state.regs dst).setWidth 32).rotateLeft count
        else (state.regs r).setWidth 32
      | .shr32 dst count =>
        if r = dst then ((state.regs dst).setWidth 32) >>> count
        else (state.regs r).setWidth 32
      | .lea32 dst base index scale disp =>
        if r = dst then
          (state.regs base).setWidth 32 +
            (match index with | none => 0 | some i => (state.regs i).setWidth 32 <<< scale) +
            disp.setWidth 32
        else (state.regs r).setWidth 32
      | .bswap32 dst =>
        if r = dst then K256.Proofs.Verify.Hash.Compression.bswap32 ((state.regs dst).setWidth 32)
        else (state.regs r).setWidth 32 := by
  cases operation with
  | store32 | store64 | addStack32 => rfl
  | lea32 dst base index scale disp =>
    simp only [Op.eval, low_writeReg, low_extend, low_add]
    cases index with
    | none => rfl
    | some i => simp only [BitVec.setWidth_shiftLeft_of_le (by decide : 32 ≤ 64)]
  | mov32 | binary32 | not32 | rol32 | shr32 | bswap32 =>
    simp only [Op.eval, low_writeReg, low_extend]
  | mov64 => simp only [Op.eval, low_writeReg, Source.low_read64]

theorem Op.stack_eval (operation : Op) (context : ValueContext) (state : Values) (offset : Nat) :
    (operation.eval context state).stack offset =
      match operation with
      | .store32 off src =>
        if offset = off then (state.regs src).setWidth 32 else state.stack offset
      | .store64 off src =>
        if offset = off+4 then (state.regs src).extractLsb' 32 32
        else if offset = off then (state.regs src).setWidth 32 else state.stack offset
      | .addStack32 off src =>
        if offset = off then state.stack off + (state.regs src).setWidth 32 else state.stack offset
      | _ => state.stack offset := by
  cases operation <;> rfl

end K256.Proofs.Verify.Hash.Compression.Values
