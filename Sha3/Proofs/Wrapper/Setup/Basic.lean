import Sha3.Proofs.Wrapper.Invariant
import X86Proofs.Program.Compose

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def ImageAt (p : BitVec 64) (bytes : List UInt8) : Prop :=
  ∀ x ∈ codeRange p bytes, x.1.toNat < userAddressLimit ∧
    Extracted.programSections.fetchByte x.1 = some x.2

theorem ImageAt.code {p : BitVec 64} {bytes : List UInt8} {s : RamState}
    (h : ImageAt p bytes) (loaded : ProgramLoaded s) : CodeIn (codeRange p bytes) s :=
  fun x hx ↦ ⟨(h x hx).1, programLoaded_fetchByte loaded (h x hx).2⟩

theorem ImageAt.slice {p : BitVec 64} {all bytes : List UInt8} (h : ImageAt p all)
    (offset : Nat) (hslice : (all.drop offset).take bytes.length = bytes) :
    ImageAt (p + BitVec.ofNat 64 offset) bytes :=
  fun x hx ↦ h x (codeRange_mem_of_drop offset hslice x hx)

def Mode.outputSlotOffset (mode : Mode) (v : Variant)
    (_keccak : Bool := false) (fullState : Bool := false) : Nat :=
  match mode, fullState, v with
  | .plain, true, _ => 0
  | .plain, false, .sha224 | .plain, false, .sha256 => 32
  | .plain, false, .sha384 => 48
  | .plain, false, .sha512 => 64
  | .reset, _, _ => 0
  | .digest, true, _ => 208
  | .digest, false, _ => 0
  | .finalizeReset, _, _ | .digestFinalizeIntoReset, _, _ => 16
  | .finalizeFixedReset, true, _ | .digestFinalizeReset, true, _ => 24
  | .finalizeFixedReset, false, _ | .digestFinalizeReset, false, _ => 16

def outputSlot (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  frameBase initial v mode keccak fullState +
    BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState)

structure SetupRegisters (initial : RamState) (v : Variant) (mode : Mode) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Prop where
  stack : stackPtr s = frameBase initial v mode keccak fullState
  destination : (Operand.reg 7 : Operand 64).read s = statePointer initial v mode keccak fullState
  length : (Operand.reg 2 : Operand 64).read s = 201
  value : (Operand.reg 6 : Operand 64).read s = 0

structure SetupArguments (initial : RamState) (v : Variant) (mode : Mode) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Prop where
  pointers : (Operand.reg (if mode = .digest then 15 else 12) : Operand 64).read s =
    initial.regValue .rdi
  lengths : (Operand.reg 14 : Operand 64).read s =
    initial.regValue (if mode = .digest then .rsi else .rdx)
  count : match mode with
    | .digest => True
    | _ => (Operand.reg 15 : Operand 64).read s = initial.regValue .rsi
  modeValues : match mode with
    | .plain => (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
        initial.regValue .rcx
    | .reset => (Operand.reg 13 : Operand 64).read s = initial.regValue .r8 ∧
        (Operand.reg 3 : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
          initial.regValue .rcx
    | .digest => (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx ∧
        (Operand.reg 12 : Operand 64).read s = statePointer initial v mode keccak fullState ∧
        (Operand.reg 5 : Operand 64).read s = initial.regValue .rbp ∧
        (fullState = false → (Operand.reg 13 : Operand 64).read s = initial.regValue .r13)
    | .finalizeReset | .digestFinalizeIntoReset =>
        (Operand.reg 3 : Operand 64).read s = initial.regValue .r8 ∧
        (Operand.reg 5 : Operand 64).read s = initial.regValue .rcx ∧
        (Operand.reg 13 : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
          initial.regValue .r9
    | .finalizeFixedReset | .digestFinalizeReset => if fullState then
        (Operand.reg 13 : Operand 64).read s = initial.regValue .r8 ∧
        (Operand.mem (frameBase initial v mode keccak fullState + 16) : Operand 64).read s =
          initial.regValue .rcx ∧
        (Operand.reg 3 : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
          initial.regValue .r9
      else if v = .sha224 ∨ v = .sha256 then
        (Operand.reg 3 : Operand 64).read s = initial.regValue .r8 ∧
        (Operand.reg 5 : Operand 64).read s = initial.regValue .rcx ∧
        (Operand.reg 13 : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
          initial.regValue .r9
      else
        (Operand.reg 13 : Operand 64).read s = initial.regValue .r8 ∧
        (Operand.reg 5 : Operand 64).read s = initial.regValue .rcx ∧
        (Operand.reg 3 : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
          initial.regValue .r9

end Sha3.Proofs.Wrapper
