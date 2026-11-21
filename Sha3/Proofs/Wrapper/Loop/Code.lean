import Sha3.Proofs.Wrapper.Loop.Layout
import Sha3.Proofs.Image
import X86Proofs.Instructions.Lea.Encode

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def nextBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.largeFollower v fullState then
    [0x4c, 0x8d, if kind.indexReg v fullState == 0 then 0x78 else 0x7b, 1]
  else match kind with
  | .plain => [0x48, 0x8d, 0x58, 1]
  | .firstReset => [0x4c, 0x8d, 0x68, 1]
  | .firstFinalizeReset | .firstFinalizeFixedReset | .firstDigestFinalizeIntoReset
  | .firstDigestFinalizeReset => [0x48, 0x8d, 0x68, 1]
  | .secondReset => [0x48, 0x8d, 0x6b, 1]
  | _ => [0x49, 0x8d, 0x5d, 1]

def pointerBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.indexReg v fullState == 0 then [0x49, 0x8b, 0x14, 0xc4]
  else if kind.indexReg v fullState == 3 then [0x49, 0x8b, 0x14, 0xdc]
  else [0x4b, 0x8b, 0x14, 0xec]

def lengthBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.indexReg v fullState == 0 then [0x49, 0x8b, 0x0c, 0xc6]
  else if kind.indexReg v fullState == 3 then [0x49, 0x8b, 0x0c, 0xde]
  else [0x4b, 0x8b, 0x0c, 0xee]

def cursorBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  match kind.cursorReg v fullState with
  | some r => if r == 13 then [0x4c, 0x89, 0xef] else [0x48, 0x89, 0xef]
  | none => [0x48, 0x8d, 0xbc, 0x24] ++ immBytes 32 (BitVec.ofNat 32 (kind.cursorStackOffset v fullState))

def stateBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.stateReg v fullState == 3 then [0x48, 0x89, 0xde]
  else if kind.stateReg v fullState == 13 then [0x4c, 0x89, 0xee]
  else [0x48, 0x89, 0xee]

def indexBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.largeFollower v fullState then
    [0x4c, 0x89, if kind.indexReg v fullState == 0 then 0xf8 else 0xfb]
  else match kind with
  | .plain => [0x48, 0x89, 0xd8]
  | .firstReset => [0x4c, 0x89, 0xe8]
  | .firstFinalizeReset | .firstFinalizeFixedReset | .firstDigestFinalizeIntoReset
  | .firstDigestFinalizeReset => [0x48, 0x89, 0xe8]
  | .secondReset => [0x48, 0x89, 0xeb]
  | _ => [0x49, 0x89, 0xdd]

def compareBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  if kind.memoryBound v fullState then
    if fullState then [0x4c, 0x39, 0x7c, 0x24, 8] else [0x4c, 0x39, 0x3c, 0x24]
  else if kind.largeFollower v fullState then [0x4c, 0x39, 0xfb]
  else match kind with
  | .plain | .secondFinalizeReset | .secondFinalizeFixedReset | .secondDigestFinalizeIntoReset
  | .secondDigestFinalizeReset => [0x49, 0x39, 0xdf]
  | .firstReset => [0x4c, 0x39, 0xeb]
  | .secondReset => [0x49, 0x39, 0xef]
  | _ => [0x49, 0x39, 0xed]

def branchBytes (kind : Kind) (v : Variant := .sha256) (fullState : Bool := false) : List UInt8 :=
  [0x75, UInt8.ofNat (kind.branchDisp v fullState).toNat]

def callBytes (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : List UInt8 :=
  0xe8 :: immBytes 32 (kind.callDisp v (keccak := keccak) (fullState := fullState))

def bytes (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : List UInt8 :=
  nextBytes kind v fullState ++ pointerBytes kind v fullState ++ lengthBytes kind v fullState ++ cursorBytes kind v fullState ++ stateBytes kind v fullState ++
    callBytes kind v (keccak := keccak) (fullState := fullState) ++ indexBytes kind v fullState ++ compareBytes kind v fullState ++ branchBytes kind v fullState

theorem code_subset (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState)) (bytes kind v (keccak := keccak) (fullState := fullState)), x ∈ Extracted.programImage := by
  have ha : kind.start v (keccak := keccak) (fullState := fullState) = Extracted.textAddress +
      BitVec.ofNat 64 ((kind.start v (keccak := keccak) (fullState := fullState)).toNat - 0x100000) := by
    cases fullState <;> cases keccak <;> cases kind <;> cases v <;> rfl
  have hb : (kind.start v (keccak := keccak) (fullState := fullState)).toNat - 0x100000 + (kind.endOffset v fullState) ≤ Extracted.textBytes.size := by
    cases fullState <;> cases keccak <;> cases kind <;> cases v <;> first | decide +kernel | cases hfull rfl
  have hs : Extracted.textBytes.toListFrom ((kind.start v (keccak := keccak) (fullState := fullState)).toNat - 0x100000) (kind.endOffset v fullState) =
      bytes kind v (keccak := keccak) (fullState := fullState) := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> first | decide +kernel | cases hfull rfl
  rw [ha]
  exact textSlice_subset_programImage hb hs

theorem slice_subset (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) (offset : Nat) (part : List UInt8)
    (hs : ((bytes kind v (keccak := keccak) (fullState := fullState)).drop offset).take part.length = part) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 offset) part,
      x ∈ Extracted.programImage :=
  fun x hx ↦ code_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) x (codeRange_mem_of_drop offset hs x hx)

theorem next_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState)) (nextBytes kind v fullState), x ∈ Extracted.programImage := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 0 (nextBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem pointer_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + 4) (pointerBytes kind v fullState), x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 4 (pointerBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem length_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + 8) (lengthBytes kind v fullState), x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 8 (lengthBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem cursor_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + 12) (cursorBytes kind v fullState), x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) 12 (cursorBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem state_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.stateOffset v fullState)) (stateBytes kind v fullState),
      x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.stateOffset v fullState) (stateBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem call_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState)) (callBytes kind v (keccak := keccak) (fullState := fullState)),
      x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.callOffset v fullState) (callBytes kind v (keccak := keccak) (fullState := fullState)) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem index_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.returnOffset v fullState)) (indexBytes kind v fullState),
      x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.returnOffset v fullState) (indexBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem compare_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.compareOffset v fullState)) (compareBytes kind v fullState),
      x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.compareOffset v fullState) (compareBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem branch_code (kind : Kind) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (hfull : fullState = true → v = .sha256 := by simp_all) :
    ∀ x ∈ codeRange (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.branchOffset v fullState)) (branchBytes kind v fullState),
      x ∈ Extracted.programImage :=
  slice_subset kind v (keccak := keccak) (fullState := fullState) (hfull := hfull) (kind.branchOffset v fullState) (branchBytes kind v fullState) (by cases fullState <;> cases kind <;> cases v <;> rfl)

theorem inProgram (kind : Kind) (v : Variant) {keccak : optParam Bool false} {fullState : optParam Bool false} (offset : Nat)
    (ho : offset ∈ [0, 4, 8, 12, (kind.stateOffset v fullState), (kind.callOffset v fullState), (kind.returnOffset v fullState),
      (kind.compareOffset v fullState), (kind.branchOffset v fullState), (kind.endOffset v fullState)]) (hfull : fullState = true → v = .sha256 := by simp_all) :
    InProgram (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 offset) := by
  let byte := Extracted.textBytes.getD ((kind.start v (keccak := keccak) (fullState := fullState)).toNat - 0x100000 + offset)
  refine ⟨byte, imageSections_mem_toCodeMap_of_fetchByte ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases fullState <;> cases keccak <;> cases kind <;> cases v <;> first | decide +kernel | cases hfull rfl

end Sha3.Proofs.Wrapper.Loop
