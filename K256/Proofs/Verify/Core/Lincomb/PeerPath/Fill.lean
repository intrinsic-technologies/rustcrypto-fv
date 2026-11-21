import K256.Proofs.Verify.Core.Lincomb.PeerPath.State
import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.Fill
import K256.Proofs.Verify.Core.Lincomb.CopyCall

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

private abbrev peerDigitPointers (fr : Activation) (x : Registers) : Registers :=
  (x.set 5 ⟨64, slot fr 8⟩).set 13 ⟨64, slot fr 0x118⟩

private theorem peerDigitPointers_five (d : Registers) :
    (peerDigitPointers fr d)[5] = ⟨64, slot fr 8⟩ := by
  unfold peerDigitPointers
  rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_self]

private theorem peerDigitPointers_thirteen (d : Registers) :
    (peerDigitPointers fr d)[13] = ⟨64, slot fr 0x118⟩ := by
  exact Vector.getElem_set_self _

private theorem peerDigitPointers_other (d : Registers) (i : Fin Reg.count)
    (h5 : 5 ≠ i.val) (h13 : 13 ≠ i.val) :
    (peerDigitPointers fr d)[i] = d[i] := by
  simp only [peerDigitPointers, Fin.getElem_fin, Vector.getElem_set_ne _ _ h5, Vector.getElem_set_ne _ _ h13]

private theorem firstPeerFillSetup {d : Registers} {n : Ram}
    (sp : d[4].get 64 = workSp fr) (target : d[3].get 64 = 0x12a700) (df : d[22].get 1 = 0)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbec 2) :
    ∃ x, program.runBlock (dialect Extracted.programImage) ⟨.l10fbd5,d,n⟩ =
        .call ⟨.l12a700,x,memStore n (workSp fr - 8) (0x10fbee : BitVec 64)⟩
          (callResume .l10fbee 0x10fbee) ∧
      FillArguments fr x (slot fr 8) ∧ PreservedByFill x (peerDigitPointers fr d) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, target, guard]
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, df⟩, ?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first
      | exact (peerDigitPointers_five d).symm
      | exact (peerDigitPointers_thirteen d).symm
      | symm
        exact peerDigitPointers_other d _ (by dsimp only; decide) (by dsimp only; decide)

private theorem secondPeerFillSetup {d : Registers} {n : Ram}
    (sp : d[4].get 64 = workSp fr) (target : d[3].get 64 = 0x12a700)
    (dst : d[13].get 64 = slot fr 0x118) (df : d[22].get 1 = 0)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbf8 2) :
    ∃ x, program.runBlock (dialect Extracted.programImage) ⟨.l10fbee,d,n⟩ =
        .call ⟨.l12a700,x,memStore n (workSp fr - 8) (0x10fbfa : BitVec 64)⟩
          (callResume .l10fbfa 0x10fbfa) ∧
      FillArguments fr x (slot fr 0x118) ∧ PreservedByFill x d := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, target, dst, guard]
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, df⟩, ?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem peerFillCall (e : Entry fr a p digest r s)
    {start after : Label} {ret : BitVec 64} {off : Nat} {d x : Registers} {n : Ram}
    (whole : RamWriteFrame fr.original n [fr.region])
    (call : program.runBlock (dialect Extracted.programImage) ⟨start,d,n⟩ =
      .call ⟨.l12a700,x,memStore n (workSp fr - 8) ret⟩ (callResume after ret))
    (fill : FillArguments fr x (slot fr off)) (bound : off + 265 ≤ 0x28a8)
    (low : ret.toNat < 2^32) :
    ∃ f t, Reaches start d n after f t ∧ f[4] = ⟨64, workSp fr⟩ ∧ PreservedByFill f x ∧
      RamWriteFrame n t (workWrites fr 8 off 265) ∧ DigitBytes t (slot fr off + 8) [] := by
  let pushed := memStore n (workSp fr - 8) ret
  have before := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at before
  have room := e.stackRoom
  have base := workNat e
  have high := e.low
  have pushFrame : RamWriteFrame n pushed (workWrites fr 8 off 265) :=
    (RamWriteFrame.refl _ _).memStore ret
      ⟨_, List.mem_cons_self .., by dsimp only [InRegion, scratch]; omega⟩
  have within : RegionsWithin (workWrites fr 8 off 265) [fr.region] := by
    intro reg hr
    obtain ⟨mid, hm, lo, hi⟩ := workWithin e (depth := 8) (off := off) (len := 265)
      (by decide) (by omega) reg hr
    obtain ⟨outer,hout,lo',hi'⟩ := (frameBounds e).1 mid hm
    exact ⟨outer,hout,Nat.le_trans lo' lo,Nat.le_trans hi hi'⟩
  have word : memLoad pushed (workSp fr - 8) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨out,run,tag,sp,keep,frame,zeros⟩ :=
    fillDigits e (whole.trans pushFrame within) fill (by omega) low word
  have exec : program.Exec (dialect Extracted.programImage) ⟨⟨.l12a700, x, pushed⟩, []⟩ out :=
    .done (by simp only [Program.step, run, Transfer.next])
  refine ⟨_, _, reachesCall call exec tag, sp, keep, ?_, zeros⟩
  exact pushFrame.trans frame (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)

private theorem afterPeerFill (e : Entry fr a p digest r s)
    {d x f : Registers} {n t : Ram} {off : Nat}
    (saved : CallerFrame fr c d m n)
    (lo : 8 ≤ off) (hi : off + 265 ≤ 0x28a8)
    (sp : f[4] = ⟨64, workSp fr⟩) (keep : PreservedByFill f x)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → x[i].width = 64)
    (fixed : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → x[i] = d[i])
    (frame : RamWriteFrame n t (workWrites fr 8 off 265)) :
    CallerFrame fr c f m t := by
  refine CallerFrame.next e saved (by decide) lo hi frame sp ?_ ?_
  · intro i hi
    rw [keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact widths i hi
  · intro i hi
    exact (keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans (fixed i hi)

theorem fillPeerDigits (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) {d n}
    (saved : CallerFrame fr c d m n) (generator : GeneratorCopy fr n u) (regs : PreparesPeer fr d 0x1568) :
    ∃ f t, Reaches .l10fbd5 d n .l10fbfa f t ∧ CallerFrame fr c f m t ∧
      GeneratorCopy fr t u ∧ PreparesPeer fr f 8 ∧
      DigitBytes t (slot fr 8 + 8) [] ∧ DigitBytes t (slot fr 8 + 0x118) [] := by
  have whole := h.frame.trans saved.frame (frameBounds e).1
  have guard₁ : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbec 2 :=
    ParseSignature.storeOk_of_codeRange (off := 23) (belowWrite e whole (depth := 8) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l10fbd5 x hx)) (by decide)
  have df : d[22].get 1 = 0 := congrArg (Value.get 1)
    ((saved.fixedRegs 22 (by decide)).trans ((args.keep 22 (by decide)).trans h.df))
  obtain ⟨x,call₁,fill₁,setup₁⟩ := firstPeerFillSetup (congrArg (Value.get 64) saved.sp)
    (congrArg (Value.get 64) regs.1) df guard₁
  obtain ⟨d₁,n₁,run₁,sp₁,keep₁,frame₁,zeros₁⟩ := peerFillCall e whole call₁ fill₁ (by decide) (by decide)
  have kept₁ : PreservedByFill d₁ (peerDigitPointers fr d) := fun i hi =>
    (keep₁ i hi).trans (setup₁ i hi)
  have widths₁ (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :
      (peerDigitPointers fr d)[i].width = 64 := by
    by_cases h5 : 5 = i.val
    · obtain rfl : i = 5 := Fin.ext h5.symm
      exact congrArg Value.width (peerDigitPointers_five d)
    by_cases h13 : 13 = i.val
    · obtain rfl : i = 13 := Fin.ext h13.symm
      exact congrArg Value.width (peerDigitPointers_thirteen d)
    rw [peerDigitPointers_other _ _ h5 h13]
    exact saved.widths i hi
  have fixed₁ (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) :
      (peerDigitPointers fr d)[i] = d[i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact peerDigitPointers_other _ _ (by omega) (by omega)
  have saved₁ := afterPeerFill e saved (by decide) (by decide) sp₁ kept₁ widths₁ fixed₁ frame₁
  have whole₁ := h.frame.trans saved₁.frame (frameBounds e).1
  have guard₂ : StoreOk Extracted.programImage n₁ (workSp fr - 8) 8 0x10fbf8 2 :=
    ParseSignature.storeOk_of_codeRange (off := 10) (belowWrite e whole₁ (depth := 8) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l10fbee x hx)) (by decide)
  have bx : d₁[3] = ⟨64, 0x12a700⟩ :=
    ((kept₁ 3 (by decide)).trans (peerDigitPointers_other d 3 (by decide) (by decide))).trans regs.1
  have di : d₁[13] = ⟨64, slot fr 0x118⟩ :=
    (kept₁ 13 (by decide)).trans (peerDigitPointers_thirteen d)
  have df₁ := (congrArg (Value.get 1) ((kept₁ 22 (by decide)).trans
    (fixed₁ 22 (by decide)))).trans df
  obtain ⟨y,call₂,fill₂,setup₂⟩ := secondPeerFillSetup (congrArg (Value.get 64) sp₁)
    (congrArg (Value.get 64) bx) (congrArg (Value.get 64) di) df₁ guard₂
  obtain ⟨f,t,run₂,sp₂,keep₂,frame₂,zeros₂⟩ := peerFillCall e whole₁ call₂ fill₂ (by decide) (by decide)
  have kept₂ : PreservedByFill f d₁ := fun i hi => (keep₂ i hi).trans (setup₂ i hi)
  have saved₂ := afterPeerFill e saved₁ (by decide) (by decide) sp₂ kept₂ saved₁.widths
    (fun _ _ => rfl) frame₂
  have keepPeer (i : Fin Reg.count) (hi : i.val ∈ [3,12,14,15]) : f[i] = d[i] := by
    have both := (kept₂ i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (kept₁ i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact both.trans (peerDigitPointers_other _ _ (by omega) (by omega))
  have bp : f[5] = ⟨64, slot fr 8⟩ :=
    ((kept₂ 5 (by decide)).trans (kept₁ 5 (by decide))).trans (peerDigitPointers_five d)
  have keepGenerator {n' t' : Ram} {off : Nat} (frame : RamWriteFrame n' t' (workWrites fr 8 off 265))
      (stored : GeneratorCopy fr n' u) (apart : off + 265 ≤ 0xbc8) : GeneratorCopy fr t' u :=
    stored.of_copy
      (Copied.of_frame frame (workOutside e (by decide) (by decide) (by omega) (.inr apart)))
      (Copied.of_frame frame (workOutside e (by decide) (by decide) (by omega) (.inr (by omega))))
  refine ⟨f,t,run₁.trans run₂,saved₂,keepGenerator frame₂ (keepGenerator frame₁ generator (by decide)) (by decide),
    ⟨(keepPeer 3 (by decide)).trans regs.1, (keepPeer 12 (by decide)).trans regs.2.1,
      (keepPeer 14 (by decide)).trans regs.2.2.1, (keepPeer 15 (by decide)).trans regs.2.2.2.1,
      bp⟩, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    have same := frame₂.memLoad_eq (k := 8)
      (workOutside e (k := 16 + i.val) (by decide) (by omega) (by decide) (.inl (by omega)))
    have addr : slot fr (16 + i.val) = slot fr 8 + 8 + BitVec.ofNat 64 i.val := by
      simp only [slot, BitVec.ofNat_add, BitVec.add_assoc]
      bv_omega
    rw [addr] at same
    exact same.trans (zeros₁ i)
  · have addr : slot fr 8 + 0x118 = slot fr 0x118 + 8 := by unfold slot; bv_omega
    rw [addr]
    exact zeros₂

end K256.Proofs.Verify.Core.Lincomb
