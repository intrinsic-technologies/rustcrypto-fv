import Sha3.Proofs.Wrapper.Layout

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program

inductive Kind where
  | plain | firstReset | firstFinalizeReset | secondReset | secondFinalizeReset
  | firstFinalizeFixedReset | secondFinalizeFixedReset
  | firstDigestFinalizeIntoReset | secondDigestFinalizeIntoReset
  | firstDigestFinalizeReset | secondDigestFinalizeReset
  deriving DecidableEq

namespace Kind

def mode : Kind → Mode
  | .plain => .plain
  | .firstReset | .secondReset => .reset
  | .firstFinalizeReset | .secondFinalizeReset => .finalizeReset
  | .firstFinalizeFixedReset | .secondFinalizeFixedReset => .finalizeFixedReset
  | .firstDigestFinalizeIntoReset | .secondDigestFinalizeIntoReset => .digestFinalizeIntoReset
  | .firstDigestFinalizeReset | .secondDigestFinalizeReset => .digestFinalizeReset

theorem mode_ne_digest (kind : Kind) : kind.mode ≠ .digest := by
  cases kind <;> decide

def largeFollower (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Bool :=
  match kind with
  | .firstFinalizeFixedReset | .secondFinalizeFixedReset
  | .firstDigestFinalizeReset | .secondDigestFinalizeReset =>
    fullState || v == .sha384 || v == .sha512
  | _ => false

def indexReg (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  match kind with
  | .plain | .firstReset | .firstFinalizeReset | .firstFinalizeFixedReset
  | .firstDigestFinalizeIntoReset | .firstDigestFinalizeReset => 0
  | .secondReset => 3
  | .secondFinalizeReset | .secondDigestFinalizeIntoReset => 13
  | .secondFinalizeFixedReset | .secondDigestFinalizeReset =>
    if kind.largeFollower v fullState then 3 else 13

def nextReg (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  if kind.largeFollower v fullState then 15 else
  match kind with
  | .plain | .secondFinalizeReset | .secondFinalizeFixedReset
  | .secondDigestFinalizeIntoReset | .secondDigestFinalizeReset => 3
  | .firstReset => 13
  | _ => 5

def boundReg (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  if kind.largeFollower v fullState then 3 else
  match kind with
  | .plain | .secondReset | .secondFinalizeReset | .secondFinalizeFixedReset
  | .secondDigestFinalizeIntoReset | .secondDigestFinalizeReset => 15
  | .firstReset => 3
  | _ => 13

def memoryBound (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Bool :=
  match kind with
  | .secondFinalizeFixedReset | .secondDigestFinalizeReset => kind.largeFollower v fullState
  | _ => false

def boundOperand (kind : Kind) (s : RamState) (v : Variant := .sha256)
    (fullState : Bool := false) : Operand 64 :=
  if kind.memoryBound v fullState then
    .mem ((Operand.reg 4 : Operand 64).read s + if fullState then 8 else 0)
  else .reg (kind.boundReg v fullState)

def stateReg (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  if kind.largeFollower v fullState then 13 else
  match kind with
  | .firstFinalizeReset | .firstFinalizeFixedReset | .firstDigestFinalizeIntoReset
  | .firstDigestFinalizeReset => 3
  | .secondReset => 13
  | _ => 5

def cursorReg (kind : Kind) (v : Variant := .sha256)
    (fullState : Bool := false) : Option (BitVec 5) :=
  if kind.largeFollower v fullState then some 5 else
  match kind with
  | .plain => some 13
  | _ => none

def cursorStackOffset (kind : Kind) (_v : Variant := .sha256)
    (_fullState : Bool := false) : Nat :=
  match kind with
  | .firstReset | .secondReset => 208
  | .firstFinalizeFixedReset | .secondFinalizeFixedReset
  | .firstDigestFinalizeReset | .secondDigestFinalizeReset => 464
  | _ => 224

def stateOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  if (kind.cursorReg v fullState).isSome then 15 else 20

def callOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  kind.stateOffset v fullState + 3

def returnOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  kind.callOffset v fullState + 5

def compareOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  kind.returnOffset v fullState + 3

def branchOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  kind.compareOffset v fullState + if kind.memoryBound v fullState then
    (if fullState then 5 else 4) else 3

def endOffset (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : Nat :=
  kind.branchOffset v fullState + 2

def branchDisp (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : BitVec 8 :=
  -BitVec.ofNat 8 (kind.endOffset v fullState)

def start (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  (kind.mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (match kind with
    | .plain => 0x50
    | .firstReset => 0x60
    | .firstFinalizeReset | .firstDigestFinalizeIntoReset => 0x70
    | .secondReset => 0xa0
    | .secondFinalizeReset | .secondDigestFinalizeIntoReset => 0xb0
    | .firstFinalizeFixedReset | .firstDigestFinalizeReset =>
      if kind.largeFollower v fullState then 0x80 else 0x70
    | .secondFinalizeFixedReset | .secondDigestFinalizeReset =>
      if fullState then 0x110 else match v with
      | .sha224 => 0x110 | .sha256 => 0x120 | .sha384 => 0x160 | .sha512 => 0x1a0)

def exit (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  kind.start v keccak fullState + BitVec.ofNat 64 (kind.endOffset v fullState)

def callDisp (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : BitVec 32 :=
  (v.updateAddress - (kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState))).setWidth 32

theorem callTarget (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    kind.start v keccak fullState + BitVec.ofNat 64 (kind.returnOffset v fullState) +
      (kind.callDisp v keccak fullState).signExtend 64 = v.updateAddress := by
  cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide +kernel

theorem index_ne_next (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) :
    kind.indexReg v fullState ≠ kind.nextReg v fullState := by
  cases fullState <;> cases kind <;> cases v <;> decide +kernel

theorem bound_ne_next (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) :
    kind.boundReg v fullState ≠ kind.nextReg v fullState := by
  cases fullState <;> cases kind <;> cases v <;> decide +kernel

theorem state_ne_next (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) :
    kind.stateReg v fullState ≠ kind.nextReg v fullState := by
  cases fullState <;> cases kind <;> cases v <;> decide +kernel

end Kind

def prefixClobbers (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List Component :=
  [.reg (kind.nextReg v fullState), .reg 2, .reg 1, .reg 7, .reg 6, .rip]

def suffixClobbers (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List Component :=
  [.reg (kind.indexReg v fullState), .flags, .rip]

end Sha3.Proofs.Wrapper.Loop
