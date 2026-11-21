import K256.Proofs.Verify.Core.Lincomb.Prepare.TableBlocks
import K256.Proofs.Verify.Core.Lincomb.Loop.Add
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Operands

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

abbrev stepWrites (sp dst acc : BitVec 64) : List MemoryRegion :=
  [scratch sp 544, ⟨dst.toNat,120⟩, ⟨acc.toNat,120⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem additionStep (j : Bool) (i : Fin 7) {a : Registers} {m : Ram}
    {sp tables acc delta : BitVec 64} {p d : Projective}
    (rsp : a[4].get 64 = sp) (table : a[3].get 64 = tables)
    (cur : a[14].get 64 = acc) (dbl : a[15].get 64 = delta)
    (df : a[22] = ⟨1,0⟩) (widths : ParseSignature.ArgumentWidths a)
    (saved : ∀ k : Fin Reg.count, k.val ∈ [3,5,12,13,14,15] → a[k].width = 64)
    (mx : a[39].width = 32) (ft : a[50].width = 16) (fc : a[51].width = 16)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (align : sp.toNat % 16 = 0) (room : 544 ≤ sp.toNat)
    (stack : Writable Extracted.programImage m (sp - 544) 544)
    (left : Writable Extracted.programImage m acc 120) (right : Readable m delta 120)
    (slot : Writable Extracted.programImage m (tableSlot tables j i) 120)
    (dstApart : Outside [scratch sp 544, ⟨acc.toNat,120⟩, ⟨delta.toNat,120⟩] (tableSlot tables j i) 120)
    (accAbove : sp.toNat ≤ acc.toNat) (deltaAbove : sp.toNat ≤ delta.toNat)
    (apart : acc.toNat + 120 ≤ delta.toNat ∨ delta.toNat + 120 ≤ acc.toNat)
    (wp : p.Stored m acc) (wd : d.Stored m delta) :
    ∃ b n, Reaches (tableSite j i.castSucc) a m (tableSite j i.succ) b n ∧
      b[4] = ⟨64,sp⟩ ∧ ParseSignature.ArgumentWidths b ∧
      (∀ k : Fin Reg.count, k.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[k] = a[k]) ∧
      p.Stored n (tableSlot tables j i) ∧ (p.add d).Stored n acc ∧
      RamWriteFrame m n (stepWrites sp (tableSlot tables j i) acc) := by
  let dst := tableSlot tables j i
  let pc := address (tableSite j i.succ)
  let copy := memCopy m dst acc 120
  let n := memStore copy (sp-8) pc
  have st : (sp-544).toNat = sp.toNat-544 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have ps : (sp-8).toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ sp.toNat; omega))
  have retSmall : pc.toNat < 2^32 :=
    (by decide +kernel : ∀ t : Bool, ∀ k : Fin 7, (address (tableSite t k.succ)).toNat < 2^32) j i
  have slotW : Writable Extracted.programImage m (sp-8) 8 := stack.sub (by omega) (by omega)
  have accLow := left.readable.low
  have deltaLow := right.low
  have dstLow : dst.toNat + 120 ≤ 2^32 := slot.readable.low
  have ds : dst.toNat+120 ≤ sp.toNat-544 ∨ sp.toNat-544+544 ≤ dst.toNat :=
    dstApart.2 _ (List.mem_cons_self ..)
  have da : dst.toNat+120 ≤ acc.toNat ∨ acc.toNat+120 ≤ dst.toNat :=
    dstApart.2 _ (.tail _ (.head _))
  have dd : dst.toNat+120 ≤ delta.toNat ∨ delta.toNat+120 ≤ dst.toNat :=
    dstApart.2 _ (.tail _ (.tail _ (.head _)))
  obtain ⟨b,call⟩ := additionBlock j i rsp table cur dbl (congrArg (Value.get 1) df) widths left.readable slot da.symm slotW
  have cf : RamWriteFrame m copy [⟨dst.toNat,120⟩] := Sec1.Wrapper.Copy.memCopy_frame (.refl ..)
    ⟨_, .head _, Nat.le_refl _, Nat.le_refl _, by change dst.toNat + 120 ≤ 2^64; omega⟩
  have pf : RamWriteFrame copy n [⟨(sp-8).toNat,8⟩] := (.refl copy _ : RamWriteFrame copy copy _).memStore pc
    ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by change (sp-8).toNat+8 ≤ 2^64; have := sp.isLt; omega⟩
  have tag : memLoad n (sp-8) 64 = pc := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have ent : RoutineEntry b n (sp-8) 0x218 := by
    refine ⟨call.rsp, ?_, (call.keep 22 (by decide)).trans df, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      have hk' : k.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        omega
      exact (congrArg Value.width (call.keep k hk')).trans (saved k hk)
    · exact (congrArg Value.width (call.keep 39 (by decide))).trans mx
    · exact (congrArg Value.width (call.keep 50 (by decide))).trans ft
    · exact (congrArg Value.width (call.keep 51 (by decide))).trans fc
    · have w : Writable Extracted.programImage n (sp-544) 536 := ((stack.of_frame cf).of_frame pf).sub (Nat.le_refl _) (by omega)
      rw [show sp - 8 - BitVec.ofNat 64 0x218 = sp - 544 by bv_omega]
      exact w
    · exact (slotW.readable.of_frame cf).of_frame pf
    · rw [tag]; exact retSmall
    · intro v hv
      change (memStore (memStore m dst _) (sp-8) pc)[v.1]? = some v.2
      rw [memStore_getElem?_of_ne _ _ _ _ (fun k hk => Ne.symm (slotW.notCode v hv k hk)),
        memStore_getElem?_of_ne _ _ _ _ (fun k hk => Ne.symm (slot.notCode v hv k hk))]
      exact image v hv
  have copied := Generate.Generator.Multiply.Prepare.Table.copyRecord (dst := dst) wp
  have safeCopy (x : BitVec 64) (lo : x.toNat+120 ≤ 2^32) (apart' : dst.toNat+120 ≤ x.toNat ∨ x.toNat+120 ≤ dst.toNat) :
      Outside [⟨dst.toNat,120⟩] x 120 :=
    ⟨by omega, fun _ h => List.mem_singleton.mp h ▸ apart'.symm⟩
  have safePush (x : BitVec 64) (lo : x.toNat+120 ≤ 2^32) (apart' : x.toNat+120 ≤ (sp-8).toNat ∨ sp.toNat ≤ x.toNat) :
      Outside [⟨(sp-8).toNat,8⟩] x 120 :=
    ⟨by omega, fun _ h => List.mem_singleton.mp h ▸ (by dsimp only; omega)⟩
  obtain ⟨out,run,ret,stored,ws⟩ := Loop.add (dst := acc) (src := delta) ent call.widths (congrArg (Value.get 64) call.destination)
    (congrArg (Value.get 64) call.source) ((right.of_frame cf).of_frame pf) ((left.of_frame cf).of_frame pf)
    (by omega) (by omega) apart
    ((wp.of_frame cf (safeCopy acc accLow da)).of_frame pf (safePush acc accLow (Or.inr accAbove)))
    ((wd.of_frame cf (safeCopy delta deltaLow dd)).of_frame pf (safePush delta deltaLow (Or.inr deltaAbove)))
  have keep : Outside [scratch (sp-8) 536, ⟨acc.toNat,120⟩] dst 120 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · dsimp only [scratch]; omega
    · exact da
  refine ⟨_,_,reachesCall call.run run (ret.tag.trans (congrArg (fun t => some (Value.mk 64 t)) tag)),
    ret.rsp.trans (by rw [BitVec.sub_add_cancel]), ws, fun k hk => (ret.saved k hk).trans (call.keep k hk),
    (copied.of_frame pf (safePush dst dstLow (by omega))).of_frame ret.frame keep, stored, ?_⟩
  let rs := stepWrites sp dst acc
  have copiedFrame : RamWriteFrame m copy rs := (RamWriteFrame.refl m rs).trans cf (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩)
  have pre := copiedFrame.trans pf (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,by dsimp only [scratch]; omega,by dsimp only [scratch]; omega⟩)
  apply pre.trans ret.frame
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_,List.mem_cons_self,by dsimp only [scratch]; omega,by dsimp only [scratch]; omega⟩
  · exact ⟨_,.tail _ (.tail _ (.head _)),Nat.le_refl _,Nat.le_refl _⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
