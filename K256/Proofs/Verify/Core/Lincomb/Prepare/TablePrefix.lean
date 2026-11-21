import K256.Proofs.Verify.Core.Lincomb.Prepare.TableStep
import K256.Proofs.Generate.Generator.Multiply.Add
import K256.Proofs.Generate.Generator.Multiply.Double

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

abbrev prefixWrites (sp base acc : BitVec 64) (n : Nat) : List MemoryRegion :=
  [scratch sp 544, ⟨base.toNat, 120*n⟩, ⟨acc.toNat,120⟩]

def OddAt (m : Ram) (ptr : BitVec 64) (p : Standards.SECG.ECC.Curve.Point) (k : Nat) : Prop :=
  ∃ t : Projective, t.valid ∧ t.value = Naf.oddTableEntry p k ∧ t.Stored m ptr

structure TablePrefix (j : Bool) (i : Fin 8) (initial : Registers) (original : Ram)
    (sp tables acc : BitVec 64) (p : Projective) (a : Registers) (m : Ram) : Prop where
  rsp : a[4] = ⟨64,sp⟩
  arguments : ParseSignature.ArgumentWidths a
  keep : ∀ k : Fin Reg.count, k.val ∈ [3,5,12,13,14,15,22,39,50,51] → a[k] = initial[k]
  frame : RamWriteFrame original m (prefixWrites sp (tableSlot tables j 0) acc i.val)
  current : OddAt m acc p.value i.val
  cells : ∀ k < i.val, OddAt m (tableSlot tables j k) p.value k

theorem writableImage {ptr : BitVec 64} {len : Nat} {m : Ram}
    (w : Writable Extracted.programImage m ptr len) (v) (hv : v ∈ Extracted.programImage) :
    v.1.toNat+1 ≤ ptr.toNat ∨ ptr.toNat+len ≤ v.1.toNat := by
  apply Classical.byContradiction
  intro inside
  apply w.notCode v hv (v.1.toNat - ptr.toNat) (by omega)
  rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
theorem tablePrefix (j : Bool) {initial : Registers} {original : Ram} {sp tables acc delta : BitVec 64}
    {p : Projective} (rsp : initial[4] = ⟨64,sp⟩) (table : initial[3].get 64 = tables)
    (current : initial[14].get 64 = acc) (dbl : initial[15].get 64 = delta)
    (df : initial[22] = ⟨1,0⟩) (args : ParseSignature.ArgumentWidths initial)
    (saved : ∀ k : Fin Reg.count, k.val ∈ [3,5,12,13,14,15] → initial[k].width = 64)
    (mx : initial[39].width = 32) (ft : initial[50].width = 16) (fc : initial[51].width = 16)
    (loaded : ∀ x ∈ Extracted.programImage, original[x.1]? = some x.2)
    (align : sp.toNat % 16 = 0) (room : 544 ≤ sp.toNat)
    (stack : Writable Extracted.programImage original (sp - 544) 544)
    (left : Writable Extracted.programImage original acc 120) (right : Readable original delta 120)
    (slots : Writable Extracted.programImage original (tableSlot tables j 0) 960)
    (away : Outside [scratch sp 544, ⟨acc.toNat,120⟩, ⟨delta.toNat,120⟩] (tableSlot tables j 0) 960)
    (accAbove : sp.toNat ≤ acc.toNat) (deltaAbove : sp.toNat ≤ delta.toNat)
    (apart : acc.toNat + 120 ≤ delta.toNat ∨ delta.toNat + 120 ≤ acc.toNat)
    (valid : p.valid) (wp : p.Stored original acc) (wd : p.double.Stored original delta) (n : Fin 8) :
    ∃ a m, Reaches (tableSite j 0) initial original (tableSite j n) a m ∧
      TablePrefix j n initial original sp tables acc p a m := by
  let base := tableSlot tables j 0
  have bh : base.toNat + 960 ≤ 2^32 := slots.readable.low
  have pos (i : Nat) (hi : i < 8) : (tableSlot tables j i).toNat = base.toNat + 120*i := by
    have eq : tableSlot tables j i = base + BitVec.ofNat 64 (120*i) := by
      simp only [tableSlot,base,Nat.add_zero,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    exact eq ▸ toNat_add_ofNat base _ (by omega)
  have bs : base.toNat+960 ≤ sp.toNat-544 ∨ sp.toNat-544+544 ≤ base.toNat := away.2 _ (.head _)
  have ba : base.toNat+960 ≤ acc.toNat ∨ acc.toNat+120 ≤ base.toNat := away.2 _ (.tail _ (.head _))
  have bd : base.toNat+960 ≤ delta.toNat ∨ delta.toNat+120 ≤ base.toNat := away.2 _ (.tail _ (.tail _ (.head _)))
  have ah := left.readable.low
  have dh := right.low
  have stackBase : (sp-544).toNat = sp.toNat-544 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  induction n using Fin.induction with
  | zero =>
    exact ⟨initial, original, .refl _, ⟨rsp, args, fun _ _ => rfl, .refl .., ⟨p,valid,rfl,wp⟩,
      fun k hk => by simp at hk⟩⟩
  | succ i ih =>
    obtain ⟨a,m,path,s⟩ := ih
    have hi := i.isLt
    have index : i.castSucc.val = i.val := rfl
    have atSlot := pos i.val (by omega)
    let ptr := tableSlot tables j i.val
    have insideDelta : Outside (prefixWrites sp base acc i.val) delta 120 := by
      refine ⟨by omega, fun r h => ?_⟩
      simp only [prefixWrites,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl <;> dsimp only [scratch] <;> omega
    have dstApart : Outside [scratch sp 544, ⟨acc.toNat,120⟩, ⟨delta.toNat,120⟩] ptr 120 := by
      exact Generate.Generator.Affine.outside_subregion away (by change base.toNat ≤ (tableSlot tables j i).toNat; omega)
        (by change (tableSlot tables j i).toNat + 120 ≤ base.toNat + 960; omega)
    have image (v) (hv : v ∈ Extracted.programImage) : m[v.1]? = some v.2 := by
      refine (s.frame.outside _ ⟨by have := v.1.isLt; omega, fun r hr => ?_⟩).trans (loaded v hv)
      simp only [prefixWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · have := writableImage stack v hv; dsimp only [scratch]; omega
      · have wh : v.1.toNat + 1 ≤ base.toNat ∨ base.toNat + 960 ≤ v.1.toNat := writableImage slots v hv
        change v.1.toNat + 1 ≤ base.toNat ∨ base.toNat + 120*i.val ≤ v.1.toNat
        omega
      · exact writableImage left v hv
    have argSaved (k : Fin Reg.count) (hk : k.val ∈ [3,5,12,13,14,15]) : a[k].width = 64 := by
      rw [s.keep k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; omega)]
      exact saved k hk
    obtain ⟨t,tv,te,tw⟩ := s.current
    obtain ⟨b,o,step,rsp',args',keep,cell,next,frame⟩ := additionStep j i (sp := sp) (congrArg (Value.get 64) s.rsp)
      ((congrArg (Value.get 64) (s.keep 3 (by decide))).trans table)
      ((congrArg (Value.get 64) (s.keep 14 (by decide))).trans current)
      ((congrArg (Value.get 64) (s.keep 15 (by decide))).trans dbl) ((s.keep 22 (by decide)).trans df)
      s.arguments argSaved ((congrArg Value.width (s.keep 39 (by decide))).trans mx)
      ((congrArg Value.width (s.keep 50 (by decide))).trans ft)
      ((congrArg Value.width (s.keep 51 (by decide))).trans fc) image align room
      (stack.of_frame s.frame) (left.of_frame s.frame) (right.of_frame s.frame)
      ((slots.of_frame s.frame).sub (by change base.toNat ≤ (tableSlot tables j i).toNat; omega)
        (by change (tableSlot tables j i).toNat + 120 ≤ base.toNat + 960; omega))
      dstApart accAbove deltaAbove apart tw (wd.of_frame s.frame insideDelta)
    have f₁ : RegionsWithin (prefixWrites sp base acc i.val) (prefixWrites sp base acc i.succ.val) := by
      intro r hr
      simp only [prefixWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,.tail _ (.head _),Nat.le_refl _,by change base.toNat + 120*i.val ≤ base.toNat + 120*(i.val+1); omega⟩
      · exact ⟨_,.tail _ (.tail _ (.head _)),Nat.le_refl _,Nat.le_refl _⟩
    have f₂ : RegionsWithin (stepWrites sp ptr acc) (prefixWrites sp base acc i.succ.val) := by
      intro r hr
      simp only [stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,.tail _ (.head _),by change base.toNat ≤ (tableSlot tables j i).toNat; omega,
          by change (tableSlot tables j i).toNat + 120 ≤ base.toNat + 120*(i.val+1); omega⟩
      · exact ⟨_,.tail _ (.tail _ (.head _)),Nat.le_refl _,Nat.le_refl _⟩
    have full := ((RamWriteFrame.refl original _).trans s.frame f₁).trans frame f₂
    obtain ⟨dvalid,de⟩ := p.double_correct valid
    obtain ⟨v,value⟩ := t.add_correct p.double tv dvalid
    refine ⟨_,_,path.trans step,⟨rsp',args',fun k hk => (keep k hk).trans (s.keep k hk),full,
      ⟨_, v, ?_,next⟩,?_⟩⟩
    · exact value.trans (by rw [te,de]; rfl)
    · intro k hk
      change k < i.val+1 at hk
      by_cases eq : k = i.val
      · subst k; exact ⟨t,tv,te,cell⟩
      obtain ⟨u,uv,ue,stored⟩ := s.cells k (by change k < i.val; omega)
      have kth := pos k (by omega)
      refine ⟨u,uv,ue,stored.of_frame frame ⟨by omega,fun r hr => ?_⟩⟩
      simp only [stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> dsimp only [scratch] <;> omega

end K256.Proofs.Verify.Core.Lincomb.Prepare
