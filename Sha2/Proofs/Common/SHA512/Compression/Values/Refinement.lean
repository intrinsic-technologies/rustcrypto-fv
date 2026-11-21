import Sha2.Proofs.Common.SHA512.Compression.Values

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values

open X86 X86.Machine X86.UserProcess X86Proofs

structure Represents (context : ValueContext) (values : Values) (model : RamState) : Prop where
  regs : ∀ r, values.regs r = (Operand.reg r : Operand 64).read model
  stack : ∀ off, off % 8 = 0 → off + 8 ≤ 416 →
    values.stack off = memLoad model.external (context.stackPointer + BitVec.ofNat 64 off) 64
  input : ∀ off, off % 8 = 0 → off + 8 ≤ 128 →
    context.inputWords off = memLoad model.external (context.inputPointer + BitVec.ofNat 64 off) 64
  constants : ∀ off, off % 8 = 0 → off + 8 ≤ 640 →
    context.constants off = memLoad model.external (context.constantPointer + BitVec.ofNat 64 off) 64

def Address.Valid (address : Address) (bytes : Nat) : Prop :=
  match address with
  | .stack off => off % 8 = 0 ∧ off + bytes ≤ 416
  | .input off => off % 8 = 0 ∧ off + bytes ≤ 128
  | .constant off => off % 8 = 0 ∧ off + bytes ≤ 640

def Source.Valid (source : Source) (bytes : Nat) : Prop :=
  match source with
  | .mem address => address.Valid bytes
  | _ => True

namespace Represents

variable {context : ValueContext} {values : Values} {model : RamState}

theorem initial (s : RamState) : Represents (contextOfRam s) (ofRam s) s :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem of_obs {other : RamState} (h : Represents context values model) (obs : Obs model other) :
    Represents context values other := by
  refine ⟨fun r => (h.regs r).trans (obs.read_reg _), ?_, ?_, ?_⟩
  · intro off align bound
    exact (h.stack off align bound).trans (obs.read_mem _)
  · intro off align bound
    exact (h.input off align bound).trans (obs.read_mem _)
  · intro off align bound
    exact (h.constants off align bound).trans (obs.read_mem _)

theorem writeReg (h : Represents context values model) (dst : BitVec 5) (value : BitVec 64) :
    Represents context (values.writeReg dst value) ((Operand.reg dst : Operand 64).write model value) := by
  refine ⟨?_, h.stack, h.input, h.constants⟩
  intro r
  simp only [Values.writeReg, Operand.read_reg_write_reg, BitVec.setWidth_eq]
  by_cases hr : r = dst
  · subst r
    simp
  · rw [ite_eq_right hr, ite_eq_right (Ne.symm hr)]
    exact h.regs r

theorem read64 (h : Represents context values model) (address : Address)
    (valid : address.Valid 8) :
    Values.read64 context values address = memLoad model.external (address.value context) 64 := by
  cases address with
  | stack off => exact h.stack off valid.1 valid.2
  | input off => exact h.input off valid.1 valid.2
  | constant off => exact h.constants off valid.1 valid.2

theorem source_read64 (h : Represents context values model) (source : Source)
    (valid : source.Valid 8) : source.read64 context values =
      (match source with
       | .reg r => (Operand.reg r : Operand 64).read model
       | .imm value => value
       | .mem address => memLoad model.external (address.value context) 64) := by
  cases source with
  | reg r => exact h.regs r
  | imm value => rfl
  | mem address => exact h.read64 address valid

end Represents
end Sha2.Proofs.Common.SHA512.Compression.Values
