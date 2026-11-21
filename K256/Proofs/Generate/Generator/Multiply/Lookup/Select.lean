import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
open K256.Proofs.Common.Field

private theorem maskedWord (x y : Word) (choose : Bool) :
    ((y ^^^ x) &&& -((if choose then 1 else 0 : BitVec 8).setWidth 64)) ^^^ x =
      (if choose then y else x) := by
  cases choose
  · simp
  · change (_ &&& BitVec.allOnes 64) ^^^ x = y
    simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

def sourceWords (m : Ram) (base : Word) : Vector Word 15 :=
  Vector.ofFn fun i => memLoad m (wordAddr base 64 i.val) 64

private def slot (base : Word) : Nat → Word
  | 0 => base
  | i+1 => wordAddr base 64 (i+1)

private theorem slot_eq (base : Word) (i : Nat) : slot base i = wordAddr base 64 i := by
  cases i <;> simp [slot, wordAddr]

private def storeWords (dst : Word) (word : Nat → Word) (m : Ram) : Nat → Ram
  | 0 => m
  | n+1 => memStore (storeWords dst word m n) (slot dst n) (word n)

private theorem stored_load {dst : Word} {word : Nat → Word} {m : Ram}
    (n : Nat) (hn : dst.toNat + 8*n ≤ 2^32) (i : Nat) (hi : i < n) :
    memLoad (storeWords dst word m n) (wordAddr dst 64 i) 64 = word i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [storeWords, slot_eq]
    by_cases e : i = n
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · have off (j : Nat) (h : j ≤ n) :
          (wordAddr dst 64 j).toNat = dst.toNat + 8*j := by
        simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 8*j) (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [memLoad_memStore_of_rangeApart]
      · exact ih (by omega) (by omega)
      · apply RangeApart.of_toNat <;> simp only [off n (by omega), off i (by omega), Nat.reduceDiv] <;> omega

private theorem stored_frame {dst : Word} {word : Nat → Word} {m orig : Ram}
    {regions : List MemoryRegion} (f : RamWriteFrame orig m regions) (n : Nat)
    (hin : ∀ i < n, InRegions regions (slot dst i) 8) :
    RamWriteFrame orig (storeWords dst word m n) regions := by
  induction n with
  | zero => exact f
  | succ n ih =>
    exact (ih (fun i hi => hin i (by omega))).memStore _ (hin n (by omega))

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem selectBlock {a : Registers} {m : Ram} {sp left right dst ret : Word}
    (choose : Bool) (choice : (a[1].get 64).setWidth 8 = if choose then 1 else 0)
    (diWidth : a[7].width = 64)
    (rsp : a[4].get 64 = sp) (rsi : a[6].get 64 = left)
    (rdx : a[2].get 64 = right) (rdi : a[7].get 64 = dst)
    (stack : Writable Extracted.programImage m (sp - 80) 80)
    (src0 : Readable m left 120) (src1 : Readable m right 120)
    (target : Writable Extracted.programImage m dst 120)
    (room : 80 ≤ sp.toNat) (above0 : sp.toNat + 8 ≤ left.toNat)
    (above1 : sp.toNat + 8 ≤ right.toNat) (aboveD : sp.toNat + 8 ≤ dst.toNat)
    (retRead : Readable m sp 8) (retVal : memLoad m sp 64 = ret) (retLow : ret.toNat < 2^32) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l10fcc0, a, m⟩ = .returned out ∧
    out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
    (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → out.values[i] = ⟨64, a[i].get 64⟩) ∧
    (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = a[i]) ∧
    ParseSignature.ArgumentWidths out.values ∧
    RamWriteFrame m out.store [⟨(sp - 80).toNat, 80⟩, ⟨dst.toNat,120⟩] ∧
    WordsAt out.store dst 64 (sourceWords m (if choose then right else left)) := by
  let mask := -((a[1].get 64).setWidth 8 |>.setWidth 64)
  let word := fun i =>
    let x := memLoad m (slot left i) 64
    let y := memLoad m (slot right i) 64
    ((y ^^^ x) &&& mask) ^^^ x
  let saved := memStore m (sp - 8) (a[5].get 64)
  let saved := memStore saved (sp - 16) (a[15].get 64)
  let saved := memStore saved (sp - 24) (a[14].get 64)
  let saved := memStore saved (sp - 32) (a[13].get 64)
  let saved := memStore saved (sp - 40) (a[12].get 64)
  let saved := memStore saved (sp - 48) (a[3].get 64)
  let tmp := memStore saved (sp - 56) (word 0)
  let tmp := memStore tmp (sp - 64) (word 1)
  let tmp := memStore tmp (sp - 72) (word 2)
  let tmp := memStore tmp (sp - 80) (word 3)
  refine ⟨?out, ?block, ?post⟩
  case block =>
    arithmetic_segment using code_l10fcc0 [rsp, rsi, rdx, rdi, retVal]
    refine Eq.trans (ite_eq_left ⟨by slot_guard using code_l10fcc0, retLow⟩) ?_
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro ⟨i, hi⟩ membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · intro ⟨i, hi⟩ membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl|rfl|rfl|rfl <;> rfl
    · intro ⟨i, hi⟩ membership
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact diWidth
    · change RamWriteFrame m (storeWords dst word tmp 15) _
      have dstLow := target.readable.low
      have spLow := retRead.low
      have ofs (off : Word) (h : off.toNat ≤ 80) :
          (sp - off).toNat = sp.toNat - off.toNat :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
      have low := ofs 80 (by decide)
      let areas : List MemoryRegion := [⟨(sp - 80).toNat, 80⟩, ⟨dst.toNat, 120⟩]
      have stackSlot (d : Word) (hl : 8 ≤ d.toNat) (hh : d.toNat ≤ 80) :
          InRegions areas (sp - d) 8 := by
        refine ⟨_, List.mem_cons_self, ?_⟩
        change (sp - 80).toNat ≤ _ ∧ _ ≤ (sp - 80).toNat + 80 ∧ _ ≤ 2^64
        rw [ofs d hh, low]
        change sp.toNat - 80 ≤ _ ∧ _ ≤ sp.toNat - 80 + 80 ∧ _
        omega
      have outSlot (d : Word) (hh : d.toNat ≤ 112) :
          InRegions areas (dst + d) 8 := by
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        change dst.toNat ≤ _ ∧ _ ≤ dst.toNat + 120 ∧ _ ≤ 2^64
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        omega
      apply stored_frame
      · repeat' refine RamWriteFrame.memStore ?_ _ (stackSlot _ (by decide) (by decide))
        exact RamWriteFrame.refl _ _
      · intro i hi
        rw [slot_eq]
        exact outSlot (BitVec.ofNat 64 (8*i)) (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega)
    · change WordsAt (storeWords dst word tmp 15) dst 64 _
      intro i hi
      rw [stored_load 15 target.readable.low i hi]
      simp only [word, mask, choice, maskedWord, sourceWords, Vector.getElem_ofFn, slot_eq]
      cases choose <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Lookup
