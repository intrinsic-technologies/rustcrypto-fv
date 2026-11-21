import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Verify.Hash.FinalBlocks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine

abbrev Word := BitVec 64

def clearPrefix (m : Ram) (sp : Word) : Ram :=
  let m := memStore m (sp + 8) (0 : Word)
  let m := memStore m (sp + 16) (0 : Word)
  let m := memStore m (sp + 24) (0 : Word)
  let m := memStore m (sp + 32) (0 : Word)
  let m := memStore m (sp + 40) (0 : Word)
  let m := memStore m (sp + 48) (0 : Word)
  let m := memStore m (sp + 56) (0 : Word)
  m

def stage (m : Ram) (sp high ret : Word) : Ram :=
  let w := memStore m (sp + 216) high
  let w := memStore w (sp + 208) (memLoad m (sp + 56) 64)
  let w := memStore w (sp + 200) (memLoad m (sp + 48) 64)
  let w := memStore w (sp + 192) (memLoad m (sp + 40) 64)
  let w := memStore w (sp + 184) (memLoad m (sp + 32) 64)
  let w := memStore w (sp + 176) (memLoad m (sp + 24) 64)
  let w := memStore w (sp + 168) (memLoad m (sp + 16) 64)
  let w := memStore w (sp + 160) (memLoad m (sp + 8) 64)
  memStore w (sp - 8) ret

theorem stage_word (m : Ram) (sp high ret : Word) (i : Fin 8) :
    memLoad (stage m sp high ret) (wordAddr (sp + 160) 64 i.val) 64 =
      if i.val = 7 then high else memLoad m (wordAddr (sp + 8) 64 i.val) 64 := by
  finite_cases i <;>
    simp (disch := store_disch) only [stage, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceEqDiff,
      ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, memLoad_memStore_same, memLoad_memStore_of_rangeApart]

theorem stage_return (m : Ram) (sp high ret : Word) :
    memLoad (stage m sp high ret) (sp - 8) 64 = ret :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

def stageRegions (sp : Word) : List MemoryRegion :=
  [⟨(sp - 8).toNat, 8⟩, ⟨(sp + 160).toNat, 64⟩]

theorem stage_frame (m : Ram) (sp high ret : Word) (depth : 8 ≤ sp.toNat) (room : sp.toNat + 224 ≤ 2^64) :
    RamWriteFrame m (stage m sp high ret) (stageRegions sp) := by
  have slot (off : Word) (ho : 160 ≤ off.toNat ∧ off.toNat ≤ 216) :
      InRegions (stageRegions sp) (sp + off) 8 := by
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change (sp + 160).toNat ≤ (sp + off).toNat ∧
      (sp + off).toNat + 8 ≤ (sp + 160).toNat + 64 ∧ _
    simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow] at *
    omega
  have push : InRegions (stageRegions sp) (sp - 8) 8 := by
    refine ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, ?_⟩
    have := sp.isLt
    simp only [BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow]
    omega
  unfold stage
  apply RamWriteFrame.memStore _ _ push
  repeat' (apply RamWriteFrame.memStore _ _ (slot _ (by decide)))
  exact .refl _ _

theorem clearPrefix_word (m : Ram) (sp : Word) (i : Fin 7) :
    memLoad (clearPrefix m sp) (wordAddr (sp + 8) 64 i.val) 64 = 0 := by
  finite_cases i <;>
    simp (disch := store_disch) only [clearPrefix, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      Fin.val_succ, Fin.val_zero, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, memLoad_memStore_same,
      memLoad_memStore_of_rangeApart]

theorem clearPrefix_frame (m : Ram) (sp : Word) (room : sp.toNat + 64 ≤ 2^64) :
    RamWriteFrame m (clearPrefix m sp) [⟨(sp + 8).toNat, 56⟩] := by
  have slot (off : Word) (ho : 8 ≤ off.toNat ∧ off.toNat ≤ 56) :
      InRegions [⟨(sp + 8).toNat, 56⟩] (sp + off) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp + 8).toNat ≤ (sp + off).toNat ∧
      (sp + off).toNat + 8 ≤ (sp + 8).toNat + 56 ∧ _
    simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow] at *
    omega
  unfold clearPrefix
  repeat' (apply RamWriteFrame.memStore _ _ (slot _ (by decide)))
  exact .refl _ _

end K256.Proofs.Verify.Hash.FinalBlocks
