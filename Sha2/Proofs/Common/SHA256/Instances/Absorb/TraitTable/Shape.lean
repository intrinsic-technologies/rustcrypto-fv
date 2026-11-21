import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitFirst
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableLayouts
import Sha2.Proofs.Common.Machine.Relocatable

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Absorb.Blocks
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def cloneCodeLocation (p : BitVec 64) (size : Nat) : Bool :=
  decide (p = Extracted.textAddress + BitVec.ofNat 64 (p.toNat - Extracted.textAddress.toNat) ∧
    p.toNat - Extracted.textAddress.toNat + size < 71757)

def cloneSitesCode (sites : List Blocks.Site) : Bool :=
  sites.all (fun site => cloneCodeLocation site.pc (Blocks.bytes site.block).length)

theorem cloneCodeLocation_inProgram {p : BitVec 64} {size : Nat}
    (h : cloneCodeLocation p size = true) :
    Sha2.Proofs.Common.Machine.BlockInProgram p size := by
  unfold cloneCodeLocation at h
  have hp : p = Extracted.textAddress + BitVec.ofNat 64
      (p.toNat - Extracted.textAddress.toNat) := of_decide_eq_true h |>.1
  have bound := (of_decide_eq_true h).2
  rw [hp]
  exact Sha2.Proofs.Common.Machine.blockInProgram_of_textOffset _ _ bound

def cloneNextSmall (l : Table.Layout) (buffer restore : BitVec 4) : Bool :=
  match l.nextSmall with
  | [⟨pc, .move dst src⟩] => decide (pc = l.chunk.smallExit ∧ dst = restore ∧ src = buffer ∧
    (Blocks.bytes (.move dst src)).length = 3)
  | _ => false

def cloneNextLarge (l : Table.Layout) : Bool :=
  match l.nextLarge with
  | [⟨pc, .jump disp⟩] =>
      decide (pc = l.chunk.largeExit ∧
        branchTarget pc (Blocks.bytes (.jump disp)).length disp.value = l.chunk.smallExit + 3 ∧
        cloneCodeLocation pc (Blocks.bytes (.jump disp)).length = true ∧
        cloneCodeLocation (branchTarget pc (Blocks.bytes (.jump disp)).length disp.value) 0 = true)
  | _ => false

def cloneRegisterData (index source length tail restore0 : BitVec 4) : Bool :=
  decide ([index, source, length, tail, 0, 4].Pairwise (· ≠ ·)) &&
  decide ([index, source, length, tail, 1, 2, 3, 6, 7].Pairwise (· ≠ ·)) &&
  decide (restore0 ≠ index ∧ restore0 ≠ source ∧ restore0 ≠ length ∧
    restore0 ≠ 0 ∧ restore0 ≠ 4 ∧ restore0 ≠ 1 ∧ restore0 ≠ 2 ∧ restore0 ≠ 3 ∧ restore0 ≠ 6 ∧ restore0 ≠ 7)

set_option synthInstance.maxSize 256 in
set_option maxRecDepth 100000 in
def cloneData (l : Table.Layout) : Bool :=
  match l.count, l.load, l.cloneIn, l.cloneOut with
  | .stack countSlot,
    [⟨loadPC, .loadPair index source length pointers lengths⟩,
      ⟨tailPC, .loadTail tail tailAddress⟩],
    [⟨ci0, .constant c0 v0⟩, ⟨ci1, .move bsrc0 restore0⟩,
      ⟨ci2, .move dst0 restore1⟩, ⟨ci3, .move dst1 src1⟩, ⟨ci4, .clone⟩],
    [⟨co0, .incrementIndex index0⟩, ⟨co1, .constant c1 v1⟩,
      ⟨co2, .address addrReg addrMode⟩, ⟨co3, .move dst2 src2⟩,
      ⟨co4, .move dst3 restore2⟩, ⟨co5, .clone⟩,
      ⟨co6, .compareIndexStack index1 countOffset⟩,
      ⟨co7, .branch cc disp⟩] =>
      decide (
        l.index = index ∧ countSlot = 0x68 ∧
        l.chunk.bufferOffset = 0 ∧
        [0, 1, 2, 6, 7, source.setWidth 5, length.setWidth 5, tail.setWidth 5,
          restore0.setWidth 5].all (fun r => decide (r ∈ l.chunk.clobbered)) = true ∧
        l.pointerSlot = 0xd8 ∧ l.lengthSlot = 0xe0 ∧ l.storedOffset = 0x70 ∧
        l.chunk.registers.source = source ∧ l.chunk.registers.length = length ∧
        l.chunk.registers.tail = tail ∧
        l.chunk.alignedSource = source ∧ l.chunk.bufferRestore = some restore0 ∧
        l.chunk.bufferSource = some bsrc0 ∧ l.chunk.bulkSave = none ∧
        cloneRegisterData index source length tail restore0 = true ∧
        index0 = index ∧ index1 = index ∧ c0 = 1 ∧ v0 = 0xd ∧
        c1 = 1 ∧ v1 = 0xd ∧ bsrc0 = 3 ∧ restore0 = restore1 ∧
        dst0 = 7 ∧ dst1 = 6 ∧ src1 = 2 ∧ addrReg = 2 ∧
        addrMode = .sib 4 none 0 (.d8 0x70) ∧ dst2 = 7 ∧ src2 = 2 ∧
        dst3 = 6 ∧ restore2 = restore0 ∧ countOffset = .d8 0x68 ∧ cc = 4 ∧
        loadPC = l.head ∧ tailPC = l.head + 41 ∧
        (Blocks.bytes (.loadPair index source length pointers lengths)).length = 24 ∧
        (Blocks.bytes (.constant c0 v0)).length = 5 ∧
        (Blocks.bytes (.move bsrc0 restore0)).length = 3 ∧
        (Blocks.bytes (.move dst0 restore1)).length = 3 ∧
        (Blocks.bytes (.move dst1 src1)).length = 3 ∧
        (Blocks.bytes (.incrementIndex index0)).length = 3 ∧
        (Blocks.bytes (.constant c1 v1)).length = 5 ∧
        (Blocks.bytes (.address addrReg addrMode)).length = 5 ∧
        (Blocks.bytes (.move dst2 src2)).length = 3 ∧
        (Blocks.bytes (.move dst3 restore2)).length = 3 ∧
        (Blocks.bytes (.compareIndexStack index1 countOffset)).length = 5 ∧
        co7 + BitVec.ofNat 64 (Blocks.bytes (.branch cc disp)).length = l.head ∧
        l.chunk.entry = tailPC + BitVec.ofNat 64
          (Blocks.bytes (.loadTail tail tailAddress)).length ∧
        ci0 = l.head + 24 ∧ ci1 = l.head + 29 ∧ ci2 = l.head + 32 ∧
        ci3 = l.head + 35 ∧ ci4 = l.head + 38 ∧
        co0 = l.chunk.smallExit + 3 ∧ co1 = l.chunk.smallExit + 6 ∧
        co2 = l.chunk.smallExit + 11 ∧ co3 = l.chunk.smallExit + 16 ∧
        co4 = l.chunk.smallExit + 19 ∧ co5 = l.chunk.smallExit + 22 ∧
        co6 = l.chunk.smallExit + 25 ∧ co7 = l.chunk.smallExit + 30 ∧
        branchTarget co7 (Blocks.bytes (.branch cc disp)).length disp.value = l.exit ∧
        cloneSitesCode (l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge) = true ∧
        cloneCodeLocation l.head 0 = true ∧ cloneCodeLocation l.exit 0 = true ∧
        cloneCodeLocation (branchTarget co7 (Blocks.bytes (.branch cc disp)).length disp.value) 0 = true ∧
        pointers = .d32 l.pointerSlot ∧ lengths = .d32 l.lengthSlot ∧
        tailAddress = .sib 4 none 0 (.d8 0x3f) ∧
        cloneNextSmall l bsrc0 restore0 = true ∧ cloneNextLarge l = true)
  | _, _, _, _ => false

def CloneShape (l : Table.Layout) : Prop :=
  l.cloneIn ≠ [] ∧ l.cloneOut ≠ [] ∧ cloneData l = true ∧
    cloneSitesCode (l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge) = true

instance (l : Table.Layout) : Decidable (CloneShape l) := by
  unfold CloneShape
  infer_instance

theorem traitFirst_clone_shape (v : Wrapper.Variant := .sha256) : CloneShape (traitFirst v) := by
  cases v <;>
  decide +kernel

theorem traitLast_clone_shape (v : Wrapper.Variant := .sha256) : CloneShape (traitLastTable v) := by
  cases v <;>
  decide +kernel


end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def loadPrefixOf (l : Table.Layout) : List Blocks.Site :=
  l.load.take 1 ++ l.cloneIn.take 4

def loadCloneOf (l : Table.Layout) : Blocks.Site :=
  l.cloneIn[4]?.getD (traitFirst.cloneIn[4])

def loadTailOf (l : Table.Layout) : Blocks.Site :=
  l.load[1]?.getD (traitFirst.load[1])

def loadSitesOf (l : Table.Layout) : List Blocks.Site :=
  loadPrefixOf l ++ [loadCloneOf l, loadTailOf l]

def loadCodeOf (l : Table.Layout) : CodeMap :=
  (l.load ++ l.cloneIn).flatMap Blocks.Site.code

def nextCloneOf (l : Table.Layout) : Blocks.Site :=
  l.cloneOut[5]?.getD (traitFirst.cloneOut[5])

def nextCompareOf (l : Table.Layout) : Blocks.Site :=
  l.cloneOut[6]?.getD (traitFirst.cloneOut[6])

def nextBranchOf (l : Table.Layout) : Blocks.Site :=
  l.cloneOut[7]?.getD (traitFirst.cloneOut[7])

def nextPrefixOf (l : Table.Layout) (large : Bool) : List Blocks.Site :=
  (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut.take 5

def nextSitesOf (l : Table.Layout) : List Blocks.Site :=
  l.cloneOut ++ l.nextSmall ++ l.nextLarge

def nextCodeOf (l : Table.Layout) (large : Bool) : CodeMap :=
  (nextPrefixOf l large ++ [nextCloneOf l, nextCompareOf l, nextBranchOf l]).flatMap
    Blocks.Site.code

end Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb

private theorem clone_shape_split {l : Table.Layout} (h : CloneShape l) :
    l.load.length = 2 ∧ l.cloneIn.length = 5 ∧ l.cloneOut.length = 8 := by
  unfold CloneShape at h
  simp only [cloneData] at h
  split at h <;> simp_all

theorem cloneShape_load_length {l : Table.Layout} (h : CloneShape l) :
    l.load.length = 2 := (clone_shape_split h).1

theorem cloneShape_cloneIn_length {l : Table.Layout} (h : CloneShape l) :
    l.cloneIn.length = 5 := (clone_shape_split h).2.1

theorem cloneShape_cloneOut_length {l : Table.Layout} (h : CloneShape l) :
    l.cloneOut.length = 8 := (clone_shape_split h).2.2

end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Absorb.Blocks

 theorem cloneSitesCode_inProgram {sites : List Blocks.Site}
    (h : cloneSitesCode sites = true) :
    ∀ site ∈ sites, Sha2.Proofs.Common.Machine.BlockInProgram site.pc (Blocks.bytes site.block).length := by
  induction sites with
  | nil => simp
  | cons head tail ih =>
      simp only [cloneSitesCode, List.all_cons, Bool.and_eq_true] at h
      intro site member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact cloneCodeLocation_inProgram (by simpa using h.1)
      · exact ih h.2 site member

end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable

theorem cloneShape_load_sites {l : Table.Layout} (h : CloneShape l) :
    loadSitesOf l = l.load.take 1 ++ l.cloneIn ++
      [l.load[1]?.getD (traitFirst.load[1])] := by
  have hl := cloneShape_load_length h
  have hc := cloneShape_cloneIn_length h
  have hlen : l.cloneIn.length ≤ 5 := by omega
  have htake : l.cloneIn.take 4 ++ [l.cloneIn[4]'(by omega)] = l.cloneIn := by
    rw [List.take_append_getElem (by omega)]
    have heq : 4 + 1 = 5 := by decide
    rw [heq, List.take_of_length_le hlen]
  have hget : l.cloneIn[4]?.getD (traitFirst.cloneIn[4]) = l.cloneIn[4]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  have hloadget : l.load[1]?.getD (traitFirst.load[1]) = l.load[1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  simp only [loadSitesOf, loadPrefixOf, loadCloneOf, loadTailOf, hget, hloadget]
  have hinner : l.cloneIn.take 4 ++ [l.cloneIn[4], l.load[1]] =
      (l.cloneIn.take 4 ++ [l.cloneIn[4]]) ++ [l.load[1]] := by
    have hassoc := (List.append_assoc (l.cloneIn.take 4) [l.cloneIn[4]] [l.load[1]]).symm
    change l.cloneIn.take 4 ++ ([l.cloneIn[4]] ++ [l.load[1]]) =
      (l.cloneIn.take 4 ++ [l.cloneIn[4]]) ++ [l.load[1]]
    exact hassoc
  rw [List.append_assoc]
  rw [hinner, htake]
  rw [List.append_assoc]

end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Proofs.Common.Machine

theorem cloneShape_sites_code {l : Table.Layout} (h : CloneShape l) :
    cloneSitesCode (l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge) = true :=
  h.2.2.2

theorem cloneShape_load_sites_inside {l : Table.Layout} (h : CloneShape l) :
    ∀ site ∈ loadSitesOf l, BlockInProgram site.pc (Blocks.bytes site.block).length := by
  have hinside := cloneSitesCode_inProgram (cloneShape_sites_code h)
  have hl := cloneShape_load_length h
  have hc := cloneShape_cloneIn_length h
  have htail : l.load[1]?.getD (traitFirst.load[1]) = l.load[1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  intro site member
  have allmem : site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge := by
    rw [cloneShape_load_sites h] at member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    rcases member with (loadPart | clonePart) | tailPart
    · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_of_mem_take loadPart))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr clonePart)))
    · rcases tailPart with rfl
      rw [htail]
      exact Or.inl (Or.inl (Or.inl (Or.inl (List.getElem_mem (l := l.load) (n := 1) (by omega)))))
  exact hinside site allmem

end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Proofs.Common.Machine

 theorem cloneShape_load_code {l : Table.Layout} (h : CloneShape l)
    {site : Blocks.Site} (member : site ∈ loadSitesOf l) :
    ∀ x ∈ site.code, x ∈ loadCodeOf l := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨site, ?_, hx⟩
  rw [cloneShape_load_sites h] at member
  simp only [List.mem_append, List.mem_singleton] at member ⊢
  rcases member with (hp | hc) | ht
  · exact Or.inl (List.mem_of_mem_take hp)
  · exact Or.inr hc
  · subst site
    have len := cloneShape_load_length h
    rw [List.getElem?_eq_getElem (by omega)]
    exact Or.inl (List.getElem_mem (by omega))

open Sha2.Spec.Program X86Proofs

 theorem cloneShape_load_targets {l : Table.Layout} (h : CloneShape l) :
    ∀ site ∈ loadSitesOf l, match site.block with
      | .branch _ disp | .jump disp =>
        Sha2.Spec.Program.InProgram (branchTarget site.pc
          (Blocks.bytes site.block).length disp.value)
      | _ => True := by
  have data := h.2.2.1
  unfold cloneData at data
  split at data
  · rename_i he hc hl hi ho
    simp only [loadSitesOf, loadPrefixOf, loadCloneOf, loadTailOf, hl, hi]
    simp
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption
