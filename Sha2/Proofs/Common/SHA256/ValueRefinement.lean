import Sha2.Proofs.Common.SHA256.Compression.Values
import Sha2.Proofs.Common.SHA256.WordMemory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Values

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field.Montgomery.Schoolbook

structure Represents (context : ValueContext) (values : Values) (model : RamState) : Prop where
  regs : ∀ r, values.regs r = (Operand.reg r : Operand 64).read model
  stack : ∀ off, off % 4 = 0 → off + 4 ≤ 288 →
    values.stack off = memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 32
  input : ∀ off, off % 4 = 0 → off + 4 ≤ 64 →
    context.inputWords off = memLoad model.external (context.inputPointer + BitVec.ofNat 64 off) 32

def Address.Valid (address : Address) (bytes : Nat) : Prop :=
  match address with
  | .stack off => off % 4 = 0 ∧ off + bytes ≤ 288
  | .input off => off % 4 = 0 ∧ off + bytes ≤ 64

def Source.Valid (source : Source) (bytes : Nat) : Prop :=
  match source with
  | .mem address => address.Valid bytes
  | _ => True

namespace Represents

variable {context : ValueContext} {values : Values} {model : RamState}

theorem initial (s : RamState) : Represents (contextOfRam s) (ofRam s) s :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem of_obs {other : RamState} (h : Represents context values model) (obs : Obs model other) :
    Represents context values other := by
  refine ⟨fun r => (h.regs r).trans (obs.read_reg _), ?_, ?_⟩
  · intro off align bound
    exact (h.stack off align bound).trans (obs.read_mem _)
  · intro off align bound
    exact (h.input off align bound).trans (obs.read_mem _)

theorem writeReg (h : Represents context values model) (dst : BitVec 5) (value : BitVec 64) :
    Represents context (values.writeReg dst value) ((Operand.reg dst : Operand 64).write model value) := by
  refine ⟨?_, h.stack, h.input⟩
  intro r
  simp only [Values.writeReg, Operand.read_reg_write_reg, BitVec.setWidth_eq]
  by_cases hr : r = dst
  · subst r; simp
  · rw [ite_eq_right hr, ite_eq_right (Ne.symm hr)]
    exact h.regs r

theorem write32 (h : Represents context values model) (off : Nat) (value : BitVec 32)
    (align : off % 4 = 0) (bound : off + 4 ≤ 288)
    (separate : RangeApart context.stackPointer 288 context.inputPointer 64) :
    Represents context (values.write32 off value)
      ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 32).write model value) := by
  refine ⟨h.regs, ?_, ?_⟩
  · intro index indexAlign indexBound
    change (if index = off then value else values.stack index) = _
    rw [show ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 32).write model value).external =
      memStore model.external (context.stackPointer + BitVec.ofNat 64 off) value from rfl]
    rw [memLoad32_store32_aligned _ _ _ align indexAlign (by omega) (by omega)]
    split
    · rfl
    · exact h.stack index indexAlign indexBound
  · intro index indexAlign indexBound
    change _ = memLoad (memStore _ _ _) _ 32
    rw [memLoad_memStore_rangeApart]
    · exact h.input index indexAlign indexBound
    · intro a ha b hb
      have apart := separate (off+a) (by omega) (index+b) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using apart

theorem write64 (h : Represents context values model) (off : Nat) (value : BitVec 64)
    (align : off % 4 = 0) (bound : off + 8 ≤ 288)
    (separate : RangeApart context.stackPointer 288 context.inputPointer 64) :
    Represents context (values.write64 off value)
      ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 64).write model value) := by
  refine ⟨h.regs, ?_, ?_⟩
  · intro index indexAlign indexBound
    change (if index = off+4 then value.extractLsb' 32 32 else
      if index = off then value.setWidth 32 else values.stack index) = _
    rw [show ((Operand.mem (context.stackPointer + BitVec.ofNat 64 off) : Operand 64).write model value).external =
      memStore model.external (context.stackPointer + BitVec.ofNat 64 off) value from rfl]
    rw [memLoad32_store64_aligned _ _ _ align indexAlign (by omega) (by omega)]
    by_cases low : index = off
    · simp only [low, Nat.left_eq_add, Nat.reduceEqDiff, ↓reduceIte]
    · by_cases high : index = off+4
      · subst index
        simp only [ite_eq_right (by omega : off+4 ≠ off), ite_true]
      · simp only [low, high, ↓reduceIte]
        exact h.stack index indexAlign indexBound
  · intro index indexAlign indexBound
    change _ = memLoad (memStore _ _ _) _ 32
    rw [memLoad_memStore_rangeApart]
    · exact h.input index indexAlign indexBound
    · intro a ha b hb
      have apart := separate (off+a) (by omega) (index+b) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using apart

theorem read32 (h : Represents context values model) (address : Address)
    (valid : address.Valid 4) :
    Values.read32 context values address = memLoad model.external (address.value context) 32 := by
  cases address with
  | stack off => exact h.stack off valid.1 valid.2
  | input off => exact h.input off valid.1 valid.2

theorem read64 (h : Represents context values model) (address : Address)
    (valid : address.Valid 8) :
    Values.read64 context values address = memLoad model.external (address.value context) 64 := by
  cases address with
  | stack off =>
    change _ = memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 64
    change off % 4 = 0 ∧ off+8 ≤ 288 at valid
    change values.stack (off+4) ++ values.stack off =
      memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 64
    rw [h.stack (off+4) (by omega) (by omega), h.stack off valid.1 (by omega),
      memLoad64_eq_words32]
    congr 2
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  | input off =>
    change _ = memLoad model.external (context.inputPointer + BitVec.ofNat 64 off) 64
    change off % 4 = 0 ∧ off+8 ≤ 64 at valid
    change context.inputWords (off+4) ++ context.inputWords off =
      memLoad model.external (context.inputPointer + BitVec.ofNat 64 off) 64
    rw [h.input (off+4) (by omega) (by omega), h.input off valid.1 (by omega),
      memLoad64_eq_words32]
    congr 2
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl

theorem source_read32 (h : Represents context values model) (source : Source)
    (valid : source.Valid 4) : source.read32 context values =
      (match source with
       | .reg r => (Operand.reg r : Operand 32).read model
       | .imm value => value
       | .mem address => memLoad model.external (address.value context) 32) := by
  cases source with
  | reg r =>
    change (values.regs r).setWidth 32 = _
    rw [h.regs r]
    rfl
  | imm value => rfl
  | mem address => exact h.read32 address valid

theorem source_read64 (h : Represents context values model) (source : Source)
    (valid : source.Valid 8) : source.read64 context values =
      (match source with
       | .reg r => (Operand.reg r : Operand 64).read model
       | .imm value => value.setWidth 64
       | .mem address => memLoad model.external (address.value context) 64) := by
  cases source with
  | reg r => exact h.regs r
  | imm value => rfl
  | mem address => exact h.read64 address valid

end Represents

end Sha2.Proofs.Common.SHA256.Compression.Values
