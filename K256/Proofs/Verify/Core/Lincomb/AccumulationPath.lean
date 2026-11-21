import K256.Proofs.Verify.Core.Lincomb.Tables
import K256.Proofs.Verify.Core.Lincomb.Iterator
import K256.Proofs.Verify.Core.Lincomb.Loop

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

set_option maxRecDepth 4096 in
theorem accumulationPath (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hu : u < domain.n) (hv : v < domain.n)
    {f t} (saved : CallerFrame fr c f m t) (tables : PeerPrepared fr f t p u v) :
    ∃ g z, Reaches .l10fc13 f t .l10fca6 g z ∧ CallerFrame fr c g m z ∧
      ProjectiveAt z (localSp fr + 8)
        (wnafAccumulator (combinationBases p u v) 129 (fun i => Naf.digits (combinationScalars u v i))) := by
  obtain ⟨g, z, reach, fz, ptr, gen, peer⟩ := relocate e h args saved tables
  let w := workSp fr
  let sp := w - 8
  let dst := localSp fr + 8
  let table := slot fr 0x1568
  let iter := slot fr 0x228
  let n := Iterator.pushed z w
  have room := e.stackRoom
  have top := e.low
  have bottom := e.low_toNat
  have wn := workNat e
  have sn : sp.toNat = (workSp fr).toNat - 8 := belowWorkNat e (depth := 8) (by decide)
  have dn : dst.toNat = fr.rsp.toNat - 488 + 8 := ScalarProduct.slotNat e (off := 8) (by decide)
  have tn : table.toNat = fr.rsp.toNat - 10952 + 0x1568 := slotNat e (by decide)
  have pos : iter.toNat = fr.rsp.toNat - 10952 + 0x228 := slotNat e (by decide)
  have whole := h.frame.trans fz.frame (frameBounds e).1
  have rawSp := congrArg (Value.get 64) fz.sp
  change g[4].get 64 = w at rawSp
  have rawPtr := congrArg (Value.get 64) ptr
  change g[13].get 64 = w + 0x1568 at rawPtr
  obtain ⟨y,call,ry,di,si,bx,keep,writes⟩ := Iterator.setup (a := g) (sp := w) (dst := dst) (m := z) rawSp
    rawPtr fz.dest
    ((e.stack.of_frame whole).sub (by change _ ≤ sp.toNat; omega)
      (by change sp.toNat + _ ≤ _; omega))
  have f₁ : CallerFrame fr c g m n := CallerFrame.next e fz (depth := 8) (off := 0x228) (len := 72)
    (by decide) (by decide) (by decide) writes fz.sp fz.widths (fun _ _ => rfl)
  have wn' := h.frame.trans f₁.frame (frameBounds e).1
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : y[i] = b[i] :=
    ((keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      (fz.fixedRegs i hi)).trans (args.keep i
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))
  have wy (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : y[i].width = 64 := by
    by_cases h3 : i.val = 3
    · have eq : i = 3 := Fin.ext h3
      subst i
      exact congrArg Value.width bx
    · rw [keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
      exact fz.widths i hi
  obtain ⟨fst, last, l, r', ret⟩ := Iterator.fields z w
  have callEntry : RoutineEntry y n sp 0x478 :=
    routineEntry e wn' (by decide) ry wy ((preserved 22 (by decide)).trans h.df)
      (congrArg Value.width ((preserved 39 (by decide)).trans h.mxcsr))
      (congrArg Value.width ((preserved 50 (by decide)).trans h.ftw))
      (congrArg Value.width ((preserved 51 (by decide)).trans h.fcw))
      (by change (memLoad (Iterator.pushed z w) (w - 8) 64).toNat < _; rw [ret]; decide)
  have copy {off len : Nat} (fit : off + len ≤ 10952) (apart : 0x228 + 72 ≤ off) :
      Copied z (slot fr off) n (slot fr off) len :=
    Copied.of_frame writes (workOutside e (depth := 8) (off := 0x228) (len := 72)
      (by decide) fit (by decide) (Or.inr apart))
  have point₁ := gen.of_copy (copy (by decide) (by decide)) (copy (by decide) (by decide))
  have point₂ := peer.of_copy (copy (by decide) (by decide)) (copy (by decide) (by decide))
  let footprint := [scratch sp 0x478, (⟨dst.toNat, 120⟩ : MemoryRegion)]
  have apart {base : BitVec 64} {len : Nat} (lo : (workSp fr).toNat ≤ base.toNat)
      (hi : base.toNat + len ≤ dst.toNat) : Outside footprint base len := by
    refine ⟨by omega, ?_⟩
    intro reg hr
    simp only [footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [scratch] <;> omega
  have destApart : Outside [scratch sp 0x478, (⟨sp.toNat,8⟩ : MemoryRegion)] dst 120 := by
    refine ⟨by omega, ?_⟩
    intro reg hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [scratch] <;> omega
  have adds (x y : Nat) : slot fr x + BitVec.ofNat 64 y = slot fr (x+y) := by
    simp only [slot, BitVec.ofNat_add, BitVec.add_assoc]
  obtain ⟨out, run, post, point⟩ := accumulate (sp := sp) (dst := dst) (iterator := iter)
    (dataPtr := table) callEntry (congrArg (Value.get 64) di) (congrArg (Value.get 64) si)
    hu hv e.onCurve fst (by rw [show table + 0x1340 = slot fr 0x28a8 from adds 0x1568 0x1340,
      show iter + 8 = slot fr 0x230 from adds 0x228 8]; exact last)
    ⟨by rw [show iter + 16 = slot fr 0x238 from adds 0x228 16]; exact l,
     by rw [show iter + 64 = slot fr 0x268 from adds 0x228 64]; exact r'⟩
    (by intro he; rw [he] at tn; change 0 = _ at tn; omega)
    (workWrite e wn' (by decide)).readable (workWrite e wn' (by decide)).readable
    (ScalarProduct.writeSlot e wn' (off := 8) (by decide))
    (apart (by omega) (by omega)) (apart (by omega) (by omega)) destApart
    (by rw [show table + 0x780 = slot fr 0x1ce8 from adds 0x1568 0x780]; exact point₁)
    (by rw [show table + 0x9a0 = slot fr 0x1f08 from adds 0x1568 0x9a0,
      show table + 0x1120 = slot fr 0x2688 from adds 0x1568 0x1120]; exact point₂)
  have resumed := reachesCall call run
    (post.tag.trans (congrArg (fun x => some (Value.mk 64 x)) ret))
  have fits : RegionsWithin footprint (Lincomb.writes fr) := by
    have baseTop := ScalarProduct.belowNat e (off := 488) (by decide)
    change (localSp fr).toNat = _ at baseTop
    intro reg hr
    simp only [footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,by change fr.low.toNat ≤ sp.toNat - 0x478 ∧
          sp.toNat - 0x478 + 0x478 ≤ fr.low.toNat + ((localSp fr).toNat - fr.low.toNat); omega⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
  have frame : CallerFrame fr c out.values m out.store := by
    refine ⟨post.rsp.trans (by rw [show sp+8=w from BitVec.sub_add_cancel ..]), ?_, ?_,
      (post.frame.memLoad_eq (apart (Nat.le_refl _) (by change (workSp fr).toNat + 8 ≤ _; omega))).trans f₁.dest,
      ?_, ?_, f₁.frame.trans post.frame fits⟩
    · intro i hi
      exact (congrArg Value.width (post.saved i
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (wy i hi)
    · intro i hi
      exact ((post.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
        (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (fz.fixedRegs i hi)
    · intro i
      have hi := i.isLt
      have loc := slotNat e (k := 0x28a8 + 8*i.val) (by omega)
      rw [post.frame.memLoad_eq (apart (by omega) (by change _ + 8 ≤ _; omega))]
      exact f₁.saved i
    · have loc := slotNat e (k := 0x28d8) (by decide)
      exact (post.frame.memLoad_eq (apart (by omega) (by change _ + 8 ≤ _; omega))).trans f₁.ret
  exact ⟨_,_,reach.trans resumed,frame,point⟩

end K256.Proofs.Verify.Core.Lincomb
