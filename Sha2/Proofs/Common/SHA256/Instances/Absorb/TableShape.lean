import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableLayouts
import Sha2.Proofs.Reset.Layouts
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitFirst
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Shape

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

def codeLocation (p : BitVec 64) (size : Nat) : Bool :=
  decide (p = Extracted.textAddress + BitVec.ofNat 64 (p.toNat - Extracted.textAddress.toNat) ∧
    p.toNat - Extracted.textAddress.toNat + size < 71757)

theorem codeLocation_inProgram {p : BitVec 64} {size : Nat}
    (h : codeLocation p size = true) : BlockInProgram p size := by
  unfold codeLocation at h
  have hp : p = Extracted.textAddress + BitVec.ofNat 64
      (p.toNat - Extracted.textAddress.toNat) := of_decide_eq_true h |>.1
  have bound := (of_decide_eq_true h).2
  rw [hp]
  exact blockInProgram_of_textOffset _ _ bound

def noCloneNextSmall (l : Table.Layout) (index count : BitVec 4) : Bool :=
  match l.nextSmall with
  | [⟨pc₀, .incrementIndex i⟩, ⟨pc₁, .compareIndex j k⟩,
      ⟨pc₂, .branch cc disp⟩] =>
      decide (pc₀ = l.chunk.smallExit ∧ i = index ∧ pc₁ = l.chunk.smallExit + 3 ∧
        j = index ∧ k = count ∧ pc₂ = l.chunk.smallExit + 6 ∧ cc = 4 ∧
        branchTarget pc₂ 6 disp.value = l.exit ∧
        (Blocks.bytes (.branch cc disp)).length = 6 ∧ pc₂ + 6 = l.head ∧
        codeLocation pc₀ (Blocks.bytes (.incrementIndex i)).length = true ∧
        codeLocation pc₁ (Blocks.bytes (.compareIndex j k)).length = true ∧
        codeLocation pc₂ (Blocks.bytes (.branch cc disp)).length = true ∧
        codeLocation (branchTarget pc₂ (Blocks.bytes (.branch cc disp)).length disp.value) 0 = true)
  | _ => false

def noCloneNextLarge (l : Table.Layout) (index count : BitVec 4) : Bool :=
  match l.nextLarge with
  | [⟨pc₀, .incrementIndex i⟩, ⟨pc₁, .compareIndex j k⟩,
      ⟨pc₂, .branch cc disp⟩, ⟨pc₃, .jump (.short jumpValue)⟩] =>
      decide (pc₀ = l.chunk.largeExit ∧ i = index ∧ pc₁ = l.chunk.largeExit + 3 ∧
        j = index ∧ k = count ∧ pc₂ = l.chunk.largeExit + 6 ∧ cc = 5 ∧
        branchTarget pc₂ 6 disp.value = l.head ∧
        (Blocks.bytes (.branch cc disp)).length = 6 ∧ pc₃ = l.chunk.largeExit + 12 ∧
        jumpValue = 0xe ∧ l.head ≠ pc₃ ∧
        branchTarget pc₃ 2 (Blocks.Displacement.short jumpValue).value = l.exit ∧
        codeLocation pc₀ (Blocks.bytes (.incrementIndex i)).length = true ∧
        codeLocation pc₁ (Blocks.bytes (.compareIndex j k)).length = true ∧
        codeLocation pc₂ (Blocks.bytes (.branch cc disp)).length = true ∧
        codeLocation pc₃ (Blocks.bytes (.jump (.short jumpValue))).length = true ∧
        codeLocation (branchTarget pc₂ (Blocks.bytes (.branch cc disp)).length disp.value) 0 = true ∧
        codeLocation (branchTarget pc₃ (Blocks.bytes (.jump (.short jumpValue))).length
          (Blocks.Displacement.short jumpValue).value) 0 = true)
  | _ => false

def noCloneBufferSource (source length tail : BitVec 4) : Option (BitVec 4) → Bool
  | none => true
  | some r => decide (r ≠ source ∧ r ≠ length ∧ r ≠ tail ∧ r ≠ 0)

def noCloneData (l : Table.Layout) : Bool :=
  match l.count, l.load with
  | .reg count, [⟨pc₀, .loadPair index _source _length pointers lengths⟩,
      ⟨pc₁, .loadTail _tail address⟩] =>
      decide (l.index = index ∧ codeLocation l.head 0 = true ∧ codeLocation l.exit 0 = true ∧
        l.chunk.registers.source = _source ∧
        l.chunk.registers.length = _length ∧ l.chunk.registers.tail = _tail ∧
        l.storedOffset = l.chunk.bufferOffset ∧
        l.pointerSlot < 2 ^ 31 ∧ l.lengthSlot < 2 ^ 31 ∧ l.chunk.bufferRestore = none ∧
        l.chunk.bufferOffset + 63 < 128 ∧
        [index, _source, _length, _tail, count, 0, 4].Pairwise (· ≠ ·) ∧
        (∀ r ∈ [0, _source, _length, _tail], r.setWidth 5 ∈ l.chunk.clobbered) ∧
        noCloneBufferSource _source _length _tail l.chunk.bufferSource = true ∧
        pc₀ = l.head ∧ pc₁ = l.head + 24 ∧
        l.chunk.entry = pc₁ + BitVec.ofNat 64
          (Blocks.bytes (.loadTail _tail address)).length ∧
        codeLocation pc₀ (Blocks.bytes (.loadPair index _source _length pointers lengths)).length = true ∧
        codeLocation pc₁ (Blocks.bytes (.loadTail _tail address)).length = true ∧
        pointers = .d32 l.pointerSlot ∧ lengths = .d32 l.lengthSlot ∧
        address = .sib 4 none 0 (.d8 (l.chunk.bufferOffset + 63)) ∧
        noCloneNextSmall l index count = true ∧ noCloneNextLarge l index count = true)
  | _, _ => false

def NoCloneShape (l : Table.Layout) : Prop :=
  l.cloneIn = [] ∧ l.cloneOut = [] ∧ noCloneData l = true

instance (l : Table.Layout) : Decidable (NoCloneShape l) := by
  unfold NoCloneShape
  infer_instance

theorem resetDiscarded_noClone (v : Wrapper.Variant := .sha256) : NoCloneShape (Sha2.Proofs.Reset.resetDiscarded v) := by
  cases v <;> decide +kernel

theorem resetFirst_noClone (v : Wrapper.Variant := .sha256) : NoCloneShape (Sha2.Proofs.Reset.resetFirst v) := by
  cases v <;> decide +kernel

theorem resetSecond_noClone (v : Wrapper.Variant := .sha256) : NoCloneShape (Sha2.Proofs.Reset.resetSecond v) := by
  cases v <;> decide +kernel

theorem finalizeFirst_noClone (v : Wrapper.Variant := .sha256) : NoCloneShape (finalizeFirstTable v) := by
  cases v <;>
  decide +kernel

theorem finalizeLast_noClone (v : Wrapper.Variant := .sha256) : NoCloneShape (finalizeLastTable v) := by
  cases v <;>
  decide +kernel

end Sha2.Proofs.Common.SHA256.Instances.Absorption
