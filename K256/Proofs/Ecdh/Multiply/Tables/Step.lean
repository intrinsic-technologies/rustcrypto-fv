import K256.Proofs.Ecdh.Multiply.Frame
import K256.Proofs.Ecdh.Multiply.Split.Memory
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Step

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

private theorem peerRegionArg {k : Nat} {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (limit : k+120 ≤ 0xc10) :
    RegionsWithin (stepWrites (sp fr) k) (coreWrites fr) := by
  have depth := entry.room
  change 3800 ≤ fr.rsp.toNat at depth
  have qn : (sp fr).toNat = fr.rsp.toNat - 3256 := Split.Caller.peerSpNat entry
  have low := Split.Caller.peerLowNat entry
  intro r hr
  refine ⟨fr.region,.head _,?_⟩
  simp only [stepWrites,copyWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [Activation.region,low,qn] <;> omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem peerAddStep (add : type_of% @addCall) (first : Bool) (i : Fin 7)
    {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective} {p t : Projective}
    (entry : PeerCoreEntry fr initial d peer) (s : State (site first i.castSucc) fr a m)
    (args : Inputs first i (sp fr) a)
    (base : p.Stored m (sp fr + baseOffset first))
    (prev : t.Stored m (if i.val = 0 then sp fr + baseOffset first else sp fr+0x1d0)) :
    ∃ b n, Reaches (site first i.castSucc) a m (site first i.succ) b n ∧
      State (site first i.succ) fr b n ∧ (p.add t).Stored n (sp fr+0x1d0) ∧
      t.Stored n (ptr (sp fr) (entryOff first i)) ∧
      RamWriteFrame m n (stepWrites (sp fr) (entryOff first i)) ∧
      ∀ j : Fin Reg.count, j.val ∈ Activation.calleeSavedNumbers → b[j] = savedReg first i (sp fr) a j := by
  let q := sp fr
  let k := entryOff first i
  have small := i.isLt
  have kb : 0x490 ≤ k ∧ k+120 ≤ 0xc10 := by cases first <;> dsimp [k,entryOff] <;> omega
  have room := entry.room
  have high := entry.high
  change 3800 ≤ fr.rsp.toNat at room
  have qn : q.toNat = fr.rsp.toNat - 3256 := Split.Caller.peerSpNat entry
  have qh : q.toNat+3256 < 2^32 := by omega
  have ss : q - 544 = fr.rsp - 3800 := by dsimp [q,sp]; bv_omega
  have qback : (q-8).toNat = q.toNat-8 := BitVec.toNat_sub_of_le (by change 8 ≤ q.toNat; omega)
  have childLow : (q-8-536).toNat = q.toNat-544 := by
    rw [show q-8-536=q-544 by bv_omega]; exact BitVec.toNat_sub_of_le (by change 544 ≤ q.toNat; omega)
  have atoms := s.atoms
  rw [siteFrame] at atoms
  obtain ⟨rsp,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,stack,_⟩ := atoms
  change Writable Extracted.programImage m (fr.rsp-3800) 3800 at stack
  have win : Writable Extracted.programImage m (q-544) 3800 := ss ▸ stack
  obtain ⟨b,c⟩ := blockFor first i a m q win (by omega) qh s.widths args
  have ⟨pAt,tAt,entryAt,frame⟩ := copied first i (Nat.le_of_lt qh) base prev
  let tag := address (site first i.succ)
  let nm := memStore (copyOperands first i q m) (q-8) tag
  let childFr := child fr b nm tag
  have tagLow : tag.toNat < 2^32 := (by decide +kernel : ∀ f : Bool, ∀ j : Fin 7, (address (site f j.succ)).toNat < 2^32) first i
  have contained : RegionsWithin (copyWrites q k) (stepWrites q k) :=
    fun r h => ⟨r,.tail _ h,Nat.le_refl _,Nat.le_refl _⟩
  have full : RamWriteFrame m nm (stepWrites q k) := by
    apply ((RamWriteFrame.refl m _).trans frame contained).memStore
    refine ⟨_,.head _,?_⟩
    change q.toNat-544 ≤ (q-8).toNat ∧ (q-8).toNat + 8 ≤ q.toNat-544+544 ∧ (q-8).toNat+8 ≤ 2^64
    omega
  have within := peerRegionArg entry kb.2
  have written := s.frame.trans full within
  have bSaved : SavedWidths b := by
    intro j hj
    rw [c.saved j hj]
    unfold savedReg
    split <;> (try split) <;> (try split) <;> first | rfl | exact s.savedWidths j hj
  have atChild : Atom.All Extracted.programImage b nm (Fn10a410.frameAt .l10a410 childFr) :=
    peerChildEntry entry Fn10a410.frameInfo rfl (by decide) c.widths bSaved c.rsp
      ((c.ctrl 22 (by decide)).trans df) ((c.ctrl 39 (by decide)).trans mx)
      ((c.ctrl 50 (by decide)).trans ft) ((c.ctrl 51 (by decide)).trans fc)
      written (memLoad_memStore_same _ _ _ (by decide) (by decide)) tagLow
  have dest : childFr.rdi = q+464 := c.dst
  have source : childFr.rsi = q+296 := c.src
  have top : childFr.rsp = q-8 := rfl
  have win' := win.of_frame full
  have un : (q+464).toNat = q.toNat+464 := ptrNat (Nat.le_of_lt qh) (by decide)
  have vn : (q+296).toNat = q.toNat+296 := ptrNat (Nat.le_of_lt qh) (by decide)
  have wn : (q-544).toNat = q.toNat-544 := BitVec.toNat_sub_of_le (by change 544 ≤ q.toNat; omega)
  have en : (ptr q k).toNat = q.toNat+k := ptrNat (Nat.le_of_lt qh) (by omega)
  have push : RamWriteFrame (copyOperands first i q m) nm [⟨(q-8).toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore tag ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by change (q-8).toNat + 8 ≤ 2^64; omega⟩
  have pushed {z : Projective} {x : BitVec 64} (atX : z.Stored (copyOperands first i q m) x)
      (lo : q.toNat ≤ x.toNat) (hi : x.toNat+120 ≤ 2^64) : z.Stored nm x :=
    atX.of_frame push ⟨hi, fun r hr => List.mem_singleton.mp hr ▸ Or.inr (by dsimp only; omega)⟩
  obtain ⟨out,exec,ret,done_,widths,pSum,childFrame⟩ := add Common.fnCode_subset_programImage childFr b nm p t atChild
    (by rw [source]; apply win'.readable.sub <;> omega) (by rw [dest]; apply win'.sub <;> omega)
    (by rw [top,source]; omega) (by rw [top,dest]; omega) (by rw [dest,source]; omega)
    (dest ▸ pushed pAt (by omega) (by omega)) (source ▸ pushed tAt (by omega) (by omega))
  rw [top,dest] at childFrame
  rw [dest] at pSum
  have after : RamWriteFrame m out.store (stepWrites q k) := by
    apply full.trans childFrame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact ⟨_,.head _,by dsimp only; rw [childLow]; omega,by dsimp only; rw [childLow]; omega⟩
    · obtain rfl := List.mem_singleton.mp ht
      exact ⟨_,.tail _ (.tail _ (.tail _ (.tail _ (.head _)))),by dsimp only; omega,by dsimp only; omega⟩
  have post := s.frame.trans after within
  obtain ⟨osp,keep⟩ := Sample.sampleChildReturn (base := childBase fr b) (a := b) (tag := tag) (m := nm) done_
  have same (j : Fin Reg.count) (hj : j.val ∈ Activation.calleeSavedNumbers) : out.values[j] = b[j] := by
    have h := bSaved j hj
    have eqv (v : Value) (w : v.width = 64) : Value.mk 64 (v.get 64) = v := by
      cases v with | mk width bits => cases w; rfl
    obtain ⟨j,hj'⟩ := j
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact (keep _ (by simp [Sample.nonzeroPreserved])).trans (eqv _ h)
  have control (j : Fin Reg.count) (hj : j.val ∈ [4,22,39,50,51]) : out.values[j] = a[j] := by
    obtain ⟨j,hj'⟩ := j
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl
    · change out.values[4] = ⟨64,sp fr-8+8⟩ at osp
      rw [BitVec.sub_add_cancel] at osp
      exact osp.trans rsp.symm
    all_goals first | exact (keep _ (by simp [Sample.nonzeroPreserved])).trans df.symm | exact (keep _ (by simp [Sample.nonzeroPreserved])).trans mx.symm
                    | exact (keep _ (by simp [Sample.nonzeroPreserved])).trans ft.symm | exact (keep _ (by simp [Sample.nonzeroPreserved])).trans fc.symm
  have last : (fr.rsp-48).toNat = fr.rsp.toNat - 48 := BitVec.toNat_sub_of_le (by change 48 ≤ fr.rsp.toNat; omega)
  have rest := frameAtoms s.atoms (siteFrame ..) (siteFrame first i.succ fr) after
    (by
      simp only [Outside, BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reduceSub, Nat.reduceLeDiff, stepWrites, copyWrites, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, Nat.add_le_add_iff_right, forall_eq]
      omega) (by omega) (entry.loaded_of_frame post) control
  refine ⟨_,_,Sample.reachesAfterSampleCall c.run exec ret [],⟨rest,widths,?_,post,?_⟩,pSum,?_,after,?_⟩
  · exact fun j hj => (congrArg Value.width (same j hj)).trans (bSaved j hj)
  · apply s.locals.of_frame after
    intro kv h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [Outside, show sp fr = q from rfl, BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.reduceLeDiff, stepWrites, copyWrites, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, Nat.add_le_add_iff_right, forall_eq]
      omega
  · apply (pushed (x := ptr q k) entryAt (by omega) (by omega)).of_frame childFrame
    simp only [Outside, en, Nat.reducePow, Nat.reduceLeDiff, BitVec.ofNat_eq_ofNat, BitVec.toNat_sub,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod, BitVec.toNat_add, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  · exact fun j hj => (same j hj).trans (c.saved j hj)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
