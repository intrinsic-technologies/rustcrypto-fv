import K256.Proofs.Verify.Core.Lincomb.Double
import K256.Proofs.Verify.Core.Lincomb.Prepare.SecondDouble
import K256.Proofs.Verify.Core.Lincomb.Prepare.TableGeometry

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC
open Generate.Generator.Multiply (Projective)
open Generate.Curve

structure SecondStart (a : Registers) (n : Ram) (sp tables : BitVec 64) (p : Curve.Point) (k : Nat)
    (b : Registers) (o : Ram) : Prop extends SavedFrame a sp tables b o where
  writes : RamWriteFrame n o (tableWrites sp tables)
  arguments : ParseSignature.ArgumentWidths b
  acc : b[14] = ⟨64,accumulator sp true⟩
  delta : b[15] = ⟨64,increment sp⟩
  firstTable : ∀ i : Fin 8, OddAt o (tableSlot tables false i) (signedBase (first k) p) i.val
  secondPoint : ∃ t : Projective, t.valid ∧ t.value = signedBase (second k) (endomorphism p) ∧
    t.Stored o (accumulator sp true) ∧ t.double.Stored o (increment sp)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1750000 in
theorem firstTable {a b : Registers} {m n : Ram} {sp tables digits : BitVec 64} {p : Curve.Point} {k : Nat}
    (e : TableLayout a m sp tables digits) (bases : Bases a m sp tables digits p k b n) :
    ∃ c o, Reaches .l10f82a b n .l10f918 c o ∧ SecondStart a n sp tables p k c o := by
  obtain ⟨l,lv,le,ls,ld⟩ := bases.firstPoint
  obtain ⟨r,rv,re,rs⟩ := bases.secondPoint
  have initial : RamWriteFrame m n (allWrites sp tables digits) :=
    (RamWriteFrame.refl m _).trans bases.frame (by table_within e)
  obtain ⟨c,o,path,pre⟩ := e.prefix false bases.toSavedFrame initial bases.arguments bases.acc bases.delta lv ls ld
  have stack := (e.entry.stack.of_frame initial).of_frame pre.frame
  have tw := (e.tableWrite.of_frame initial).of_frame pre.frame
  have df := ((pre.keep 22 (by decide)).trans (bases.control 22 (by decide))).trans e.entry.df
  obtain ⟨v,call⟩ := secondDoubleCall (q := frameSp sp) (tables := tables) (congrArg (Value.get 64) pre.rsp)
    (congrArg (Value.get 64) ((pre.keep 3 (by decide)).trans bases.tableBase))
    (congrArg (Value.get 64) ((pre.keep 14 (by decide)).trans bases.acc))
    (congrArg (Value.get 1) df) (stack.readable.sub (by table_bounds e) (by table_bounds e))
    (tw.sub (by table_bounds e) (by table_bounds e)) (by table_bounds e)
    (stack.sub (by table_bounds e) (by table_bounds e))
  let copy := memCopy o (tables+0x348) (frameSp sp+0x178) 120
  let push := memStore copy (frameSp sp-8) (0x10f918 : BitVec 64)
  let childWrites := [scratch (frameSp sp-8) 0x298, ⟨(increment sp).toNat,120⟩]
  have cf : RamWriteFrame o copy [⟨(tables+0x348).toNat,120⟩] :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl ..) ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by table_bounds e⟩
  have pf : RamWriteFrame copy push [⟨(frameSp sp-8).toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore (0x10f918 : BitVec 64) ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by table_bounds e⟩
  have tag : memLoad push (frameSp sp-8) 64 = 0x10f918 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have upto := ((RamWriteFrame.refl n _).trans pre.frame (e.prefixWithin false)).trans cf (by table_within e)
  have before := upto.trans pf (by table_within e)
  have whole := initial.trans before e.tableWithin
  have same (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,22,39,50,51]) : v[i] = b[i] :=
    (call.keep i hi).trans (pre.keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : v[i] = a[i] :=
    (same i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (bases.control i hi)
  have saved (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : v[i].width = 64 := by
    by_cases x : i.val = 14
    · obtain rfl : i = 14 := Fin.ext x
      exact congrArg Value.width call.acc
    by_cases x' : i.val = 15
    · obtain rfl : i = 15 := Fin.ext x'
      exact congrArg Value.width call.delta
    rw [same i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact bases.widths i hi
  have args : RoutineEntry v push (frameSp sp-8) 0x298 := by
    have aligned := e.entry.aligned
    have access := e.entry.stack.of_frame whole
    refine ⟨call.rsp,saved,(control 22 (by decide)).trans e.entry.df,
      (congrArg Value.width (control 39 (by decide))).trans e.entry.mxcsr,
      (congrArg Value.width (control 50 (by decide))).trans e.entry.ftw,
      (congrArg Value.width (control 51 (by decide))).trans e.entry.fcw,
      by table_bounds e, by table_bounds e, access.sub (by table_bounds e) (by table_bounds e),
      access.readable.sub (by table_bounds e) (by table_bounds e),by rw [tag]; decide,e.loaded whole⟩
  have r0 := rs.of_frame pre.frame (by table_outside e)
  have r1 := r0.of_frame cf (by table_outside e)
  have r2 := r1.of_frame pf (by table_outside e)
  have access := e.entry.stack.of_frame whole
  obtain ⟨out,run,ret,widths,doubled⟩ := doubleWithWidths (dst := increment sp) (src := accumulator sp true) args
    (congrArg (Value.get 64) call.dst) (congrArg (Value.get 64) call.src)
    (access.readable.sub (by table_bounds e) (by table_bounds e))
    (access.sub (by table_bounds e) (by table_bounds e)) (by table_outside e) (by table_outside e) r2 rv
  have after : RamWriteFrame push out.store childWrites := ret.frame
  have total := before.trans ret.frame (by table_within e)
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : out.values[i] = b[i] :=
    (ret.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      (same i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))
  have final := e.savedAfter bases.toSavedFrame total (ret.rsp.trans (by rw [BitVec.sub_add_cancel]))
    ((ret.saved 3 (by decide)).trans ((same 3 (by decide)).trans bases.tableBase))
    (fun i hi => (congrArg Value.width (ret.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (saved i hi)) preserved
  have step := reachesCall call.run run (ret.tag.trans (congrArg (fun t => some (Value.mk 64 t)) tag))
  refine ⟨_,_,path.trans step,⟨final,total,widths,(ret.saved 14 (by decide)).trans call.acc,
    (ret.saved 15 (by decide)).trans call.delta,?_,
    ⟨r,rv,re,r2.of_frame ret.frame (by table_outside e),doubled⟩⟩⟩
  intro i
  have hi := i.isLt
  by_cases last : i.val = 7
  · obtain rfl : i = 7 := Fin.ext last
    obtain ⟨t,vt,et,st⟩ := pre.current
    have copied := Generate.Generator.Multiply.Prepare.Table.copyRecord (dst := tables+0x348) st
    have held := copied.of_frame pf (by table_outside e)
    exact ⟨t,vt,le ▸ et,held.of_frame ret.frame (by table_outside e)⟩
  · obtain ⟨t,vt,et,st⟩ := pre.cells i.val (by change i.val < 7; omega)
    have pos := e.slotNat false i
    have one := st.of_frame cf (by table_outside e)
    have two := one.of_frame pf (by table_outside e)
    exact ⟨t,vt,le ▸ et,two.of_frame ret.frame (by table_outside e)⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
