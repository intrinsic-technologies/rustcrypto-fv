import Sha3.Proofs.Wrapper.Finish.Epilogue
import Sha3.Proofs.Image
import Sha3.Proofs.Outcome

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def startOffset (v : Variant) (mode : Mode) (_keccak : Bool := false)
    (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => 0x6f
  | .reset => 0xc4
  | .finalizeReset | .digestFinalizeIntoReset => 0xd4
  | .digest => if fullState then 0x46 else if v = .sha512 then 0x45 else 0x42
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then 0x131 else match v with
    | .sha224 => 0x134 | .sha256 => 0x144 | .sha384 => 0x180 | .sha512 => 0x1c0

def epilogueOffset (v : Variant) (mode : Mode) (_keccak : Bool := false)
    (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => if fullState then 0xbe else match v with
    | .sha224 => 0xd6 | .sha256 => 0xda | .sha384 => 0x108 | .sha512 => 0x13c
  | .reset => 0xd2
  | .finalizeReset | .digestFinalizeIntoReset => 0xfc
  | .digest => if fullState then 0x91 else match v with
    | .sha224 => 0xa6 | .sha256 => 0xaa | .sha384 => 0xd8 | .sha512 => 0x10c
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then 0x159 else match v with
    | .sha224 => 0x15c | .sha256 => 0x16c | .sha384 => 0x1a8 | .sha512 => 0x1e8

def startAddress (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress +
    BitVec.ofNat 64 (startOffset v mode keccak fullState)

def epilogueAddress (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress +
    BitVec.ofNat 64 (epilogueOffset v mode keccak fullState)

def callOffset (v : Variant) (mode : Mode) (_keccak : Bool := false)
    (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => if fullState then 0x8f else match v with
    | .sha224 => 0x99 | .sha256 => 0x9a | .sha384 => 0xac | .sha512 => 0xc1
  | .reset => 0xcd
  | .finalizeReset | .digestFinalizeIntoReset => 0xf7
  | .digest => if fullState then 0x61 else match v with
    | .sha224 => 0x6d | .sha256 => 0x6e | .sha384 => 0x80 | .sha512 => 0x95
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then 0x154 else match v with
    | .sha224 => 0x157 | .sha256 => 0x167 | .sha384 => 0x1a3 | .sha512 => 0x1e3

def callAddress (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress +
    BitVec.ofNat 64 (callOffset v mode keccak fullState)

def callDisplacement (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : BitVec 32 :=
  (v.finalizeAddress keccak fullState -
    (callAddress mode v keccak fullState + 5)).setWidth 32

theorem call_next (mode : Mode) (v : Variant) (hMode : mode ≠ .plain)
    (hDigest : mode ≠ .digest := by decide) (keccak : Bool := false)
    (fullState : Bool := false) :
    callAddress mode v keccak fullState + 5 = epilogueAddress mode v keccak fullState := by
  cases mode with
  | plain => exact (hMode rfl).elim
  | digest => exact (hDigest rfl).elim
  | reset | finalizeReset | finalizeFixedReset | digestFinalizeIntoReset | digestFinalizeReset =>
    cases fullState <;> cases keccak <;> cases v <;> rfl

theorem call_target (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    branchTarget (callAddress mode v keccak fullState) 5 ((callDisplacement mode v keccak fullState).signExtend 64) =
      v.finalizeAddress keccak fullState := by cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel

theorem callCode_subset (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    ∀ x ∈ codeRange (callAddress mode v keccak fullState) (encodeCallRel32 (callDisplacement mode v keccak fullState)),
      x ∈ Extracted.programImage := by
  have haddr : callAddress mode v keccak fullState = Extracted.textAddress +
      BitVec.ofNat 64 ((callAddress mode v keccak fullState).toNat - 0x100000) := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> rfl
  have hbound : (callAddress mode v keccak fullState).toNat - 0x100000 + 5 ≤ Extracted.textBytes.size := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel
  have hbytes : Extracted.textBytes.toListFrom ((callAddress mode v keccak fullState).toNat - 0x100000) 5 =
      encodeCallRel32 (callDisplacement mode v keccak fullState) := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel
  rw [haddr]
  exact textSlice_subset_programImage hbound hbytes

theorem epilogueCode_subset (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    ∀ x ∈ epilogueCode v mode (epilogueAddress mode v keccak fullState) keccak fullState, x ∈ Extracted.programImage := by
  have haddr : epilogueAddress mode v keccak fullState = Extracted.textAddress +
      BitVec.ofNat 64 ((epilogueAddress mode v keccak fullState).toNat - 0x100000) := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> rfl
  have hbound : (epilogueAddress mode v keccak fullState).toNat - 0x100000 + (epilogueBytes v mode keccak fullState).length ≤
      Extracted.textBytes.size := by cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel
  have hbytes : Extracted.textBytes.toListFrom
      ((epilogueAddress mode v keccak fullState).toNat - 0x100000) (epilogueBytes v mode keccak fullState).length = epilogueBytes v mode keccak fullState := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel
  unfold epilogueCode
  rw [haddr]
  exact textSlice_subset_programImage hbound hbytes

theorem epiloguePop_inProgram (mode : Mode) (v : Variant) (k : Nat)
    (keccak : Bool := false) (fullState : Bool := false)
    (hk : k ≤ mode.pushCount fullState) :
    InProgram (epiloguePopPC (epilogueAddress mode v keccak fullState) k mode fullState) := by
  let byte : UInt8 := if k = 0 then 0x5b else
    if k = mode.pushCount fullState then 0xc3 else
    if mode ≠ .digest ∧ k = 5 then 0x5d else 0x41
  refine ⟨byte, imageSections_mem_toCodeMap_of_fetchByte ?_⟩
  have hle : mode.pushCount fullState ≤ 6 := by cases mode <;> cases fullState <;> decide
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;>
    first | exact (by contradiction) | decide +kernel

theorem epilogueChanges_writesWithin (regions : Vector MemoryRegion n) :
    WritesWithin epilogueChanges regions := by
  intro c hc address hcover
  simp only [epilogueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcover.elim

end Sha3.Proofs.Wrapper.Finish
