import K256.Proofs.Verify.Core.Lincomb.Prepare.State
import K256.Proofs.Verify.Core.Lincomb.Prepare.TablePrefix

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

abbrev allWrites (sp tables digits : BitVec 64) : List MemoryRegion :=
  [scratch sp 0x558, ⟨tables.toNat,1920⟩, ⟨digits.toNat,544⟩]

abbrev tableWrites (sp tables : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat-1368,1320⟩, ⟨tables.toNat,1920⟩]

abbrev accumulator (sp : BitVec 64) (j : Bool) := frameSp sp + (if j then 0x1f0 else 0x178)
abbrev increment (sp : BitVec 64) := frameSp sp + 0x38

structure TableLayout (a : Registers) (m : Ram) (sp tables digits : BitVec 64) : Prop where
  entry : RoutineEntry a m sp 0x558
  tableWrite : Writable Extracted.programImage m tables 1920
  digitsWrite : Writable Extracted.programImage m digits 544
  tableApart : Outside [scratch sp 0x558, ⟨sp.toNat,8⟩, ⟨digits.toNat,544⟩] tables 1920
  digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat,8⟩] digits 544

variable {a : Registers} {m : Ram} {sp tables digits : BitVec 64}

theorem TableLayout.bounds (e : TableLayout a m sp tables digits) :
    1368 ≤ sp.toNat ∧ sp.toNat+8 ≤ 2^32 ∧ tables.toNat+1920 ≤ 2^32 ∧ digits.toNat+544 ≤ 2^32 ∧
    (tables.toNat+1920 ≤ sp.toNat-1368 ∨ sp.toNat ≤ tables.toNat) ∧
    (tables.toNat+1920 ≤ sp.toNat ∨ sp.toNat+8 ≤ tables.toNat) ∧
    (digits.toNat+544 ≤ sp.toNat-1368 ∨ sp.toNat ≤ digits.toNat) ∧
    (digits.toNat+544 ≤ sp.toNat ∨ sp.toNat+8 ≤ digits.toNat) ∧
    (tables.toNat+1920 ≤ digits.toNat ∨ digits.toNat+544 ≤ tables.toNat) := by
  have room := e.entry.room
  refine ⟨room,e.entry.returnSlot.low,e.tableWrite.readable.low,e.digitsWrite.readable.low,?_,
    e.tableApart.2 _ (.tail _ (.head _)),?_,e.digitsApart.2 _ (.tail _ (.head _)),
    e.tableApart.2 _ (.tail _ (.tail _ (.head _)))⟩
  · have h := e.tableApart.2 _ (.head _)
    change _ ≤ sp.toNat-1368 ∨ sp.toNat-1368+1368 ≤ _ at h
    omega
  · have h := e.digitsApart.2 _ (.head _)
    change _ ≤ sp.toNat-1368 ∨ sp.toNat-1368+1368 ≤ _ at h
    omega

macro "table_bounds " e:ident : tactic => `(tactic| (
  obtain ⟨room,high,tabHigh,digitHigh,tabStack,tabRet,digitStack,digitRet,tabDigits⟩ :=
    TableLayout.bounds $e
  simp only [allWrites,tableWrites,prefixWrites,frameSp,tableSlot,accumulator,increment,scratch,
    Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,↓reduceIte,
    Nat.add_zero,Nat.zero_add,Nat.mul_zero,Nat.reduceMul,Nat.reduceAdd,Nat.reducePow,
    BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.reduceToNat] at *
  omega))

theorem TableLayout.loaded (e : TableLayout a m sp tables digits) {n : Ram}
    (frame : RamWriteFrame m n (allWrites sp tables digits)) :
    ∀ v ∈ Extracted.programImage, n[v.1]? = some v.2 := by
  intro v hv
  refine (frame.outside v.1 ⟨by have := v.1.isLt; omega, fun r hr => ?_⟩).trans (e.entry.image v hv)
  simp only [allWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · have h := writableImage e.entry.stack v hv
    table_bounds e
  · exact writableImage e.tableWrite v hv
  · exact writableImage e.digitsWrite v hv

theorem TableLayout.prefix (j : Bool) (e : TableLayout a m sp tables digits)
    {b : Registers} {n : Ram} {p : Projective}
    (s : SavedFrame a sp tables b n) (global : RamWriteFrame m n (allWrites sp tables digits))
    (args : ParseSignature.ArgumentWidths b) (cur : b[14] = ⟨64,accumulator sp j⟩)
    (dbl : b[15] = ⟨64,increment sp⟩)
    (valid : p.valid) (point : p.Stored n (accumulator sp j)) (twice : p.double.Stored n (increment sp)) :
    ∃ c o, Reaches (tableSite j 0) b n (tableSite j 7) c o ∧
      TablePrefix j 7 b n (frameSp sp) tables (accumulator sp j) p c o := by
  have stack := e.entry.stack.of_frame global
  have aligned := e.entry.aligned
  have table := e.tableWrite.of_frame global
  apply tablePrefix j (tables := tables) (acc := accumulator sp j) (delta := increment sp) s.rsp (congrArg (Value.get 64) s.tableBase) (congrArg (Value.get 64) cur)
    (congrArg (Value.get 64) dbl) ((s.control 22 (by decide)).trans e.entry.df) args s.widths
    ((congrArg Value.width (s.control 39 (by decide))).trans e.entry.mxcsr)
    ((congrArg Value.width (s.control 50 (by decide))).trans e.entry.ftw)
    ((congrArg Value.width (s.control 51 (by decide))).trans e.entry.fcw)
    (e.loaded global) _ _ _ _ _ _ _ _ _ _ valid point twice
  · table_bounds e
  · table_bounds e
  · apply stack.sub <;> table_bounds e
  · apply stack.sub <;> cases j <;> table_bounds e
  · apply stack.readable.sub <;> table_bounds e
  · apply table.sub <;> cases j <;> table_bounds e
  · refine ⟨by cases j <;> table_bounds e,fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> cases j <;> table_bounds e
  · cases j <;> table_bounds e
  · table_bounds e
  · cases j <;> table_bounds e


end K256.Proofs.Verify.Core.Lincomb.Prepare
