import K256.Proofs.Verify.Core.Lincomb.Prepare.FirstTable
import K256.Proofs.Verify.Core.Lincomb.Prepare.TableReturn
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC
open Generate.Generator.Multiply (Projective)
open Generate.Curve

private theorem preparedOfTables {u : Ram} {tables digits : BitVec 64} {p : Curve.Point} {k : Nat}
    (len₁ : memLoad u digits 64 = BitVec.ofNat 64 (Naf.digits (first k).natAbs).length)
    (bytes₁ : DigitBytes u (digits+8) (Naf.digits (first k).natAbs))
    (tab₁ : ∀ i : Fin 8, OddAt u (tableSlot tables false i.val) (signedBase (first k) p) i.val)
    (len₂ : memLoad u (digits+272) 64 = BitVec.ofNat 64 (Naf.digits (second k).natAbs).length)
    (bytes₂ : DigitBytes u (digits+280) (Naf.digits (second k).natAbs))
    (tab₂ : ∀ i : Fin 8, OddAt u (tableSlot tables true i.val) (signedBase (second k) (endomorphism p)) i.val) :
    Prepared u tables digits p k := by
  rintro ⟨(_|(_|j)),hj⟩
  · simp only [Nat.zero_ne_one, ↓reduceIte, Nat.mul_zero]
    rw [show digits + BitVec.ofNat 64 0 = digits by bv_omega]
    exact ⟨len₁,bytes₁,tab₁⟩
  · simp only [↓reduceIte]
    rw [show digits + BitVec.ofNat 64 272 + 8 = digits + 280 by bv_omega]
    exact ⟨len₂,bytes₂,tab₂⟩
  · omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 750000 in
private theorem preparedTables {a b c d : Registers} {m n o t u : Ram} {sp tables digits : BitVec 64}
    {p : Curve.Point} {k : Nat} {r : Projective} (e : TableLayout a m sp tables digits)
    (bases : Bases a m sp tables digits p k b n) (start : SecondStart a n sp tables p k c o)
    (re : r.value = signedBase (second k) (endomorphism p))
    (pre : TablePrefix true 7 c o (frameSp sp) tables (accumulator sp true) r d t)
    (store : u = memCopy t (tables+0x708) (accumulator sp true) 120)
    (cf : RamWriteFrame t u [⟨(tables+0x708).toNat,120⟩])
    (all : RamWriteFrame n u (tableWrites sp tables)) : Prepared u tables digits p k := by
  apply preparedOfTables (k := k) (p := p)
  · exact (all.memLoad_eq (by table_outside e)).trans bases.firstLength
  · exact Recode.digitBytes_of_frame all (by table_outside e) bases.firstBytes
  · intro i
    obtain ⟨z,zv,ze,zs⟩ := start.firstTable i
    have hi := i.isLt
    have pos := e.slotNat false i
    have held := zs.of_frame pre.frame (by table_outside e)
    exact ⟨z,zv,ze,held.of_frame cf (by table_outside e)⟩
  · exact (all.memLoad_eq (by table_outside e)).trans bases.secondLength
  · exact Recode.digitBytes_of_frame all (by table_outside e) bases.secondBytes
  · intro i
    have hi := i.isLt
    by_cases last : i.val = 7
    · obtain rfl : i = 7 := Fin.ext last
      obtain ⟨z,zv,ze,zs⟩ := pre.current
      have copied := Generate.Generator.Multiply.Prepare.Table.copyRecord (dst := tables+0x708) zs
      refine ⟨z,zv,re ▸ ze,?_⟩
      rw [store]
      exact copied
    · obtain ⟨z,zv,ze,zs⟩ := pre.cells i.val (by change i.val < 7; omega)
      have pos := e.slotNat true i
      exact ⟨z,zv,re ▸ ze,zs.of_frame cf (by table_outside e)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1750000 in
theorem finishTables {a b c : Registers} {m n o : Ram} {sp tables digits : BitVec 64}
    {p : Curve.Point} {k : Nat} (e : TableLayout a m sp tables digits)
    (bases : Bases a m sp tables digits p k b n) (start : SecondStart a n sp tables p k c o) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10f918, c, o⟩, []⟩ out ∧
      RoutineReturn a m sp 0x558 [⟨tables.toNat, 1920⟩, ⟨digits.toNat, 544⟩] out ∧
      Prepared out.store tables digits p k := by
  obtain ⟨r,rv,re,rs,rd⟩ := start.secondPoint
  have initial : RamWriteFrame m n (allWrites sp tables digits) :=
    (RamWriteFrame.refl m _).trans bases.frame (by table_within e)
  have before := initial.trans start.writes e.tableWithin
  obtain ⟨d,t,path,pre⟩ := e.prefix true start.toSavedFrame before start.arguments start.acc start.delta rv rs rd
  have prefixFrame := (RamWriteFrame.refl o _).trans pre.frame (e.prefixWithin true)
  have total := start.writes.trans prefixFrame (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have whole := initial.trans total e.tableWithin
  have final := e.savedAfter start.toSavedFrame prefixFrame pre.rsp
    ((pre.keep 3 (by decide)).trans start.tableBase)
    (fun i hi => (congrArg Value.width (pre.keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (start.widths i hi))
    (fun i hi => pre.keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))
  have retSlot := e.entry.returnSlot.of_frame whole
  have stack := e.entry.stack.of_frame whole
  have saveRead : Readable t (sp-48) 56 := by
    refine ⟨by table_bounds e, fun i hi => ?_⟩
    by_cases small : i < 48
    · have w : Readable t (sp-48) 48 := stack.readable.sub (by table_bounds e) (by table_bounds e)
      exact w.present i small
    · have h := retSlot.present (i-48) (by omega)
      rwa [show (sp-48) + BitVec.ofNat 64 i = sp + BitVec.ofNat 64 (i-48) by bv_omega]
  have ret : memLoad t sp 64 = memLoad m sp 64 := whole.memLoad_eq (by table_outside e)
  obtain ⟨out,run,store,tag,rsp,keep⟩ := tableReturn (acc := accumulator sp true) e.entry final
    (congrArg (Value.get 64) ((pre.keep 14 (by decide)).trans start.acc))
    (stack.readable.sub (by table_bounds e) (by table_bounds e))
    ((e.tableWrite.of_frame whole).sub (by table_bounds e) (by table_bounds e))
    (by table_bounds e) ret saveRead (by table_outside e)
  have cf : RamWriteFrame t out.store [⟨(tables+0x708).toNat,120⟩] := by
    rw [store]
    exact Sec1.Wrapper.Copy.memCopy_frame (.refl ..) ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by table_bounds e⟩
  have all := total.trans cf (by table_within e)
  have wholeOut := initial.trans all e.tableWithin
  refine ⟨out,Program.Exec.of_sem (path.exec run.sem),⟨tag,rsp,keep,wholeOut⟩,?_⟩
  exact preparedTables e bases start re pre store cf all

end K256.Proofs.Verify.Core.Lincomb.Prepare
