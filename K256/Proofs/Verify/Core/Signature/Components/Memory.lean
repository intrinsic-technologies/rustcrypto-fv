import K256.Proofs.Verify.Core.Signature.Components.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Components

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR

abbrev area (sp : Word) (len : Nat) : List MemoryRegion := [⟨(sp-24).toNat,len⟩]

private theorem offsetIn {sp a d : Word} {len : Nat} (low : (sp-24).toNat+len ≤ 2^32)
    (addr : a = sp + d) (fits : (d - (0 - 24)).toNat + 8 ≤ len) :
    InRegions (area sp len) a 8 := by
  have pos := toNat_of_offsets addr (addr_sub sp 24) low fits
  exact ⟨_,List.mem_cons_self,by change (sp-24).toNat ≤ a.toNat ∧ a.toNat+8 ≤ (sp-24).toNat+len ∧ _; omega⟩

macro "record_stores" low:term:max : tactic => `(tactic|
  (repeat' (refine RamWriteFrame.memStore ?_ _ (offsetIn $low (by first | rfl | apply addr_sub) (by decide)))
   exact RamWriteFrame.refl _ _))

theorem saveRegsFrame (fr : Activation) (sp : Word) (low : (sp-24).toNat+512 ≤ 2^32) :
    RamWriteFrame fr.original (saveRegs fr sp) (area sp 512) := by
  unfold saveRegs
  record_stores low

theorem saveRFrame (m : Ram) (sp : Word) (w : Vector Word 4) (low : (sp-24).toNat+312 ≤ 2^32) :
    RamWriteFrame m (saveR m sp w) (area sp 312) := by
  unfold saveR
  record_stores low

set_option maxRecDepth 2048 in
theorem stageFrame (m : Ram) (sp ret : Word) (w : Vector Word 4) (low : (sp-24).toNat+192 ≤ 2^32) :
    RamWriteFrame m (stage m sp ret w) (area sp 192) := by
  unfold stage
  record_stores low

theorem areaWithin (sp : Word) {small big : Nat} (le : small ≤ big) :
    RegionsWithin (area sp small) (area sp big) := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.add_le_add_left le _⟩

macro "read_stored_word" : tactic => `(tactic|
  simp (disch := first | decide | store_disch) only [wordAddr,Nat.reduceDiv,Nat.reduceMul,
    BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,
    memLoad_memStore_same,memLoad_memStore_of_rangeApart])

theorem stageWords (m : Ram) (sp ret : Word) (w : Vector Word 4) :
    WordsAt (stage m sp ret w) (sp+136) 64 w ∧
    WordsAt (stage m sp ret w) (sp+8) 64 (Vector.replicate 4 0) ∧
    memLoad (stage m sp ret w) (sp-8) 64 = ret := by
  unfold stage
  refine ⟨?_,?_,memLoad_memStore_same _ _ _ (by decide) (by decide)⟩
  all_goals
    intro i hi
    have vals : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases vals with rfl|rfl|rfl|rfl <;> read_stored_word <;> rfl

theorem savedRWords (m : Ram) (sp : Word) (w : Vector Word 4) :
    WordsAt (saveR m sp w) (sp+256) 64 w := by
  unfold saveR
  intro i hi
  have vals : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases vals with rfl|rfl|rfl|rfl <;> read_stored_word

structure SavedSlots (fr : Activation) (m : Ram) (sp : Word) : Prop where
  bx : memLoad m (sp+448) 64 = fr.rbx
  r12 : memLoad m (sp+456) 64 = fr.r12
  r13 : memLoad m (sp+464) 64 = fr.r13
  r14 : memLoad m (sp+472) 64 = fr.r14
  r15 : memLoad m (sp+480) 64 = fr.r15

theorem savedSlots (fr : Activation) (sp : Word) : SavedSlots fr (saveRegs fr sp) sp := by
  unfold saveRegs
  constructor <;> read_stored_word

theorem outsideAbove {sp : Word} {len off n : Nat} (low : (sp-24).toNat+512 ≤ 2^32)
    (above : len ≤ off+24) (hi : off+n ≤ 488) :
    Outside (area sp len) (sp+BitVec.ofNat 64 off) n := by
  have ofit : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  have d : (BitVec.ofNat 64 off - ((0:Word)-24)).toNat = off+24 := by
    rw [show BitVec.ofNat 64 off - ((0:Word)-24) = BitVec.ofNat 64 off + 24 by bv_omega,
      BitVec.toNat_add,ofit]
    exact Nat.mod_eq_of_lt (by change off+24 < 2^64; omega)
  have pos := toNat_of_offsets (a := sp+BitVec.ofNat 64 off) rfl (addr_sub sp 24) low
    (n := n) (by rw [d]; omega)
  rw [d] at pos
  refine ⟨by omega,fun t ht => Or.inr ?_⟩
  obtain rfl := List.mem_singleton.mp ht
  change (sp-24).toNat+len ≤ _
  omega

theorem SavedSlots.ofFrame {fr : Activation} {sp : Word} {m n : Ram} {len : Nat}
    (sv : SavedSlots fr m sp) (frame : RamWriteFrame m n (area sp len))
    (low : (sp-24).toNat+512 ≤ 2^32) (bound : len ≤ 472) : SavedSlots fr n sp := by
  have keep (off : Nat) (a : len ≤ off+24) (b : off+8 ≤ 488) :=
    frame.memLoad_eq (k := 64) (outsideAbove low a b)
  exact ⟨(keep 448 (by omega) (by decide)).trans sv.bx,(keep 456 (by omega) (by decide)).trans sv.r12,
    (keep 464 (by omega) (by decide)).trans sv.r13,(keep 472 (by omega) (by decide)).trans sv.r14,
    (keep 480 (by omega) (by decide)).trans sv.r15⟩

end K256.Proofs.Verify.Core.Components
