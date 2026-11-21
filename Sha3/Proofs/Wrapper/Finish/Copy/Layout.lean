import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.Wrapper.Finish.Code
import X86Proofs.Instructions.Lea.Triple

namespace Sha3.Proofs.Wrapper.Finish.Copy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def destinationOffset (mode : Mode) (v : Variant) (fullState : Bool := false) : Nat :=
  match mode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then 440 else match v with
      | .sha224 | .sha256 => 56 | .sha384 => 72 | .sha512 => 88
  | _ => 232

def destinationDisp (mode : Mode) (v : Variant) (fullState : Bool := false) : Disp :=
  match mode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then .d32 440 else .d8 (BitVec.ofNat 8 (destinationOffset mode v fullState))
  | _ => .d32 232

def sourceDisp (mode : Mode) (v : Variant) (fullState : Bool := false) : Disp :=
  match mode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then .d8 32 else .d32 (BitVec.ofNat 32 (mode.stateOffset v false fullState))
  | _ => .d8 24

theorem destinationDisp_value (mode : Mode) (v : Variant) (fullState : Bool) :
    (destinationDisp mode v fullState).value = BitVec.ofNat 64 (destinationOffset mode v fullState) := by
  cases mode <;> cases v <;> cases fullState <;> decide +kernel

theorem sourceDisp_value (mode : Mode) (v : Variant) (fullState : Bool)
    (hMode : mode.hasBeforeOutput = true) :
    (sourceDisp mode v fullState).value = BitVec.ofNat 64 (mode.stateOffset v false fullState) := by
  cases mode <;> cases v <;> cases fullState <;> first | contradiction | decide +kernel

theorem prefixLength (mode : Mode) (v : Variant) (fullState : Bool) :
    leaLen (.sib 4 none 0 (destinationDisp mode v fullState)) +
      leaLen (.sib 4 none 0 (sourceDisp mode v fullState)) = 13 := by
  cases mode <;> cases v <;> cases fullState <;> decide +kernel

def prefixBytes (v : Variant := .sha224) (mode : Mode := .finalizeReset)
    (fullState : Bool := false) : List UInt8 :=
  encodeLeaR64M 3 (.sib 4 none 0 (destinationDisp mode v fullState)) ++
    encodeLeaR64M 6 (.sib 4 none 0 (sourceDisp mode v fullState)) ++
    [0xba, 0xd0, 0, 0, 0, 0x48, 0x89, 0xdf]

def suffixBytes (v : Variant := .sha224) (mode : Mode := .finalizeReset) (fullState : Bool := false) : List UInt8 :=
  [0x48, 0x89, 0xdf, 0x48, 0x8b, 0x74, 0x24,
    UInt8.ofNat (mode.outputSlotOffset v false fullState)]

def callPC (v : Variant) (mode : Mode := .finalizeReset) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (startOffset v mode keccak fullState + 21)

def callDisp (v : Variant) (mode : Mode := .finalizeReset) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 32 :=
  (0x200180 - (callPC v mode keccak fullState + 6)).setWidth 32

theorem layout_bounds (mode : Mode) (v : Variant) (keccak fullState : Bool)
    (hMode : mode.hasBeforeOutput = true) :
    destinationOffset mode v fullState + 256 ≤ mode.frameSize v keccak fullState ∧
    mode.stateOffset v keccak fullState + 256 ≤ mode.frameSize v keccak fullState ∧
    (mode.stateOffset v keccak fullState + 208 ≤ destinationOffset mode v fullState ∨
      destinationOffset mode v fullState + 208 ≤ mode.stateOffset v keccak fullState) ∧
    destinationOffset mode v fullState % 8 = 0 ∧
    mode.frameSize v keccak fullState % 8 = 0 ∧
    mode.frameSize v keccak fullState + 8 < 2 ^ 32 ∧
    mode.pushCount fullState = 6 := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
    first | contradiction | decide +kernel

theorem outputSlot_bounds (mode : Mode) (v : Variant) (keccak fullState : Bool)
    (hMode : mode.hasBeforeOutput = true) :
    mode.outputSlotOffset v keccak fullState + 8 ≤ destinationOffset mode v fullState ∧
    (BitVec.ofNat 8 (mode.outputSlotOffset v keccak fullState)).signExtend 64 =
      BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState) := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
    first | contradiction | decide +kernel

theorem prefixSlices (v : Variant) (mode : Mode) (fullState : Bool) :
    let d : AddrMode := .sib 4 none 0 (destinationDisp mode v fullState)
    let r : AddrMode := .sib 4 none 0 (sourceDisp mode v fullState)
    ((prefixBytes v mode fullState).drop 0).take (0x48 :: 0x8d :: d.modrm 3 :: d.tail).length =
      (0x48 :: 0x8d :: d.modrm 3 :: d.tail) ∧
    ((prefixBytes v mode fullState).drop (leaLen d)).take (0x48 :: 0x8d :: r.modrm 6 :: r.tail).length =
      (0x48 :: 0x8d :: r.modrm 6 :: r.tail) ∧
    ((prefixBytes v mode fullState).drop (leaLen d + leaLen r)).take 5 = [0xba, 0xd0, 0, 0, 0] ∧
    ((prefixBytes v mode fullState).drop (leaLen d + leaLen r + 5)).take 3 = [0x48, 0x89, 0xdf] := by
  cases mode <;> cases fullState <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem suffixSlice (v : Variant) (mode : Mode) (keccak fullState : Bool)
    (hMode : mode.hasBeforeOutput = true) :
    let am : AddrMode := .sib 4 none 0 (.d8 (BitVec.ofNat 8 (mode.outputSlotOffset v keccak fullState)))
    ((suffixBytes v mode fullState).drop 3).take (0x48 :: 0x8b :: am.modrm 6 :: am.tail).length =
      (0x48 :: 0x8b :: am.modrm 6 :: am.tail) := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
    first | contradiction | decide +kernel

end Sha3.Proofs.Wrapper.Finish.Copy
