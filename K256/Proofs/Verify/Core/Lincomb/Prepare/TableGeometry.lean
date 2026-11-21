import K256.Proofs.Verify.Core.Lincomb.Prepare.TableLayout

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

macro "table_member " e:ident : tactic => `(tactic| (
  first
  | exact ⟨_,List.Mem.head _,by table_bounds $e,by table_bounds $e⟩
  | exact ⟨_,List.Mem.tail _ (.head _),by table_bounds $e,by table_bounds $e⟩
  | exact ⟨_,List.Mem.tail _ (.tail _ (.head _)),by table_bounds $e,by table_bounds $e⟩))

macro "table_within " e:ident : tactic => `(tactic| (
  intro r hr
  simp only [allWrites,tableWrites,prefixWrites,stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  first | (rcases hr with h|h|h <;> subst r) | (rcases hr with h|h <;> subst r) | subst r
  all_goals table_member $e))

macro "table_outside " e:ident : tactic => `(tactic| (
  refine ⟨by table_bounds $e,fun r hr => ?_⟩
  simp only [allWrites,tableWrites,prefixWrites,stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  first | (rcases hr with h|h|h <;> subst r) | (rcases hr with h|h <;> subst r) | subst r
  all_goals table_bounds $e))

variable {a : Registers} {m : Ram} {sp tables digits : BitVec 64}

theorem TableLayout.slotNat (e : TableLayout a m sp tables digits) (j : Bool) (i : Fin 8) :
    (tableSlot tables j i.val).toNat = tables.toNat + 120 * ((if j then 8 else 0) + i.val) := by
  apply toNat_add_ofNat
  have high := e.tableWrite.readable.low
  have hi := i.isLt
  cases j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem TableLayout.tableWithin (e : TableLayout a m sp tables digits) :
    RegionsWithin (tableWrites sp tables) (allWrites sp tables digits) := by table_within e

theorem TableLayout.prefixWithin (j : Bool) (e : TableLayout a m sp tables digits) :
    RegionsWithin (prefixWrites (frameSp sp) (tableSlot tables j 0) (accumulator sp j) 7)
      (tableWrites sp tables) := by cases j <;> table_within e

theorem TableLayout.savedAfter (e : TableLayout a m sp tables digits) {b c : Registers} {n o : Ram}
    (old : SavedFrame a sp tables b n) (frame : RamWriteFrame n o (tableWrites sp tables))
    (rsp : c[4] = ⟨64,frameSp sp⟩) (table : c[3] = ⟨64,tables⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64)
    (ctrl : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) :
    SavedFrame a sp tables c o := by
  have read (off : BitVec 64) (small : off.toNat ≤ 48) (fits : 8 ≤ off.toNat) :
      memLoad o (sp-off) 64 = memLoad n (sp-off) 64 := by
    apply frame.memLoad_eq
    table_outside e
  refine ⟨rsp,table,widths,fun i hi => (ctrl i hi).trans (old.control i hi),
    (read 48 (by decide) (by decide)).trans old.rbx, (read 40 (by decide) (by decide)).trans old.r12,
    (read 32 (by decide) (by decide)).trans old.r13, (read 24 (by decide) (by decide)).trans old.r14,
    (read 16 (by decide) (by decide)).trans old.r15, (read 8 (by decide) (by decide)).trans old.rbp⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
