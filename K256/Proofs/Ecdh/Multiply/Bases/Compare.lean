import K256.Proofs.Ecdh.Multiply.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Lookup.Choice
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private def firstSpans : Spans := [(0x58,8),(0x70,8),(0x50,8),(0x1d0,8)]
private def secondSpans : Spans := [(0x30,1),(0xa8,8),(0x1d0,8)]
private def firstSlots (d : Nat) : List (BitVec 64 × BitVec 64) :=
  [(0x58,(u d)[0]),(0x70,(u d)[1]),(0x50,(u d)[2]),
   (0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]
private def resultSlots (d : Nat) : List (BitVec 64 × BitVec 64) :=
  [(0x58,(u d)[0]),(0x70,(u d)[1]),(0x50,(u d)[2]),(0xa8,(v d)[0]),
   (0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]

private structure PeerFirstCompared (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop
    extends Context fr a m where
  endo : peerEndoAt fr m peer
  firstSign : a[0].get 8 = flag (firstComponent d)
  middle : a[5] = ⟨64,0x5d576e7357a4501d⟩
  top : a[3] = ⟨64,0x7fffffffffffffff⟩
  r12 : a[12] = ⟨64,(u d)[3]⟩
  r14 : a[14] = ⟨64,(v d)[0]⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩
  slots : Locals fr m (firstSlots d)

private def kept : List Nat := [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51]

private theorem choiceFlag (w : BitVec 64) (z : Int) (h : w = (flag z).setWidth 64) :
    (⟨64, ((mergeGPR 8 ((w.extractLsb' 0 8) &&& 1) ((w.extractLsb' 0 8).setWidth 64)).setWidth 8).setWidth 64⟩ : Value) =
      ⟨64,(flag z).setWidth 64⟩ := by
  rw [h]
  unfold flag
  split <;> rfl

private theorem finishChoice {fr : Activation} {initial a b : Registers} {d : Nat} {peer : Projective}
    {m pre : Ram} {l next : Label} {ret : BitVec 64} {xs : Spans} {component : Int}
    (entry : PeerCoreEntry fr initial d peer) (s : Context fr a m)
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ =
      .call ⟨.l127d50,b,memStore pre (sp fr - 8) ret⟩ (callFrame next ret))
    (brsp : b[4].get 64 = sp fr - 8) (bf : b[7] = ⟨64,(flag component).setWidth 64⟩)
    (small : ret.toNat < 2^32)
    (frame : RamWriteFrame m pre (writes fr xs))
    (bound : ∀ x ∈ xs, x.1+x.2 ≤ 3208)
    (apart : ∀ i ∈ localOffsets, Separate xs i 8)
    (args : ParseSignature.ArgumentWidths b) (saved : SavedWidths b)
    (same : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]) :
    ∃ c n, Reaches l a m next c n ∧ Context fr c n ∧
      c[0].get 8 = flag component ∧
      RamWriteFrame pre n (writes fr []) ∧ RamWriteFrame m n (writes fr xs) ∧
      ∀ i : Fin Reg.count, i.val ∈ kept → c[i] = b[i] := by
  have access := Split.Caller.peerStackAccess entry (s.frame.trans frame (peerWithin entry bound))
  have w : Writable Extracted.programImage pre (sp fr - 9) 9 :=
    Split.Caller.peerStackBelowWrite entry access (off := 9) (by decide)
  have slot : Readable pre (sp fr - 8) 8 :=
    (Split.Caller.peerStackBelowWrite entry access (off := 8) (by decide)).readable
  have tmp : Writable Extracted.programImage pre (sp fr - 8 - 1) 1 := by
    rw [show sp fr - 8 - 1 = sp fr - 9 by bv_omega]
    exact w.sub (Nat.le_refl _) (by omega)
  obtain ⟨c,n,reach,cr,cf,one,keep⟩ := Lookup.resumeChoice call brsp tmp slot small
  have under (ys : Spans) : RamWriteFrame pre n (writes fr ys) := by
    apply ((RamWriteFrame.refl pre (writes fr ys)).memStore ret
      (peerInBelow entry ys (i := 8) (by decide) (by decide))).trans one
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self ..,?_,?_⟩
    all_goals
      try dsimp only
      rw [show sp fr - 8 - 1 = sp fr - 9 by bv_omega]
      have eq : (sp fr - 9).toNat = (sp fr).toNat - 9 :=
        Split.Caller.peerStackBelowNat entry (off := 9) (by decide)
      have hs := Split.Caller.peerSpNat entry
      have room := entry.room
      change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
      change 3800 ≤ fr.rsp.toNat at room
      omega
  have whole := frame.trans (under xs) (fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩)
  have widths {ls : List Nat} (incl : ∀ i ∈ ls, i ∈ kept)
      (w : ∀ i : Fin Reg.count, i.val ∈ ls → b[i].width = 64) :
      ∀ i : Fin Reg.count, i.val ∈ ls → c[i].width = 64 := fun i h =>
    (congrArg Value.width (keep i (incl _ h))).trans (w i h)
  have keepFrame : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → c[i] = a[i] := by
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl
    · exact cr.trans s.atoms.1.symm
    all_goals exact (keep _ (by decide +revert)).trans (same _ (by decide +revert))
  refine ⟨c,n,reach,s.peerAdvance entry whole bound apart
    (widths (ls := Activation.argumentNumbers) (by decide) args)
    (widths (ls := Activation.calleeSavedNumbers) (by decide) saved) keepFrame,?_,under [],whole,keep⟩
  rw [cf,bf]
  unfold flag
  split <;> rfl

private theorem localsAfterChoice {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    {m n : Ram} {slots : List (BitVec 64 × BitVec 64)} (e : PeerCoreEntry fr initial d peer)
    (h : Locals fr m slots) (bounds : ∀ kv ∈ slots, kv.1.toNat + 8 ≤ 9500)
    (f : RamWriteFrame m n (writes fr [])) : Locals fr n slots := by
  apply h.of_frame f
  intro kv hk
  simpa only [Split.Caller.slot,Split.Caller.sp,BitVec.ofNat_toNat,BitVec.setWidth_eq,sp] using
    peerOutside e [] (bounds kv hk) (by intro x hx; cases hx)

set_option maxHeartbeats 1700000 in
set_option maxRecDepth 8192 in
private theorem firstCompare {fr : Activation} {initial a : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr initial d peer) (s : PeerComparedInput fr a m d peer) :
    ∃ c n, Reaches .l11ca7f a m .l11cb3c c n ∧ PeerFirstCompared fr c n d peer := by
  have rsp : (a[4]'(by decide)).get 64 = sp fr := congrArg (Value.get 64) s.atoms.1
  have access := Split.Caller.peerStackAccess e s.frame
  have w : Writable Extracted.programImage m (sp fr) 3256 :=
    (by simpa only [Split.Caller.slot, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      Split.Caller.peerSlotWrite e access (i := 0) (n := 3256) (by decide))
  have push := Split.Caller.peerStackBelowWrite e access (off := 8) (by decide)
  have low := w.readable.low
  have widths := s.widths
  have saved := s.savedWidths
  have r5 := congrArg (Value.get 64) s.r5
  have r3 := congrArg (Value.get 64) s.r3
  have r13 := congrArg (Value.get 64) s.r13
  have r12 := congrArg (Value.get 64) s.r12
  have h40 := s.slots (0x40,(v d)[1]) (.head _)
  have h10 := s.slots (0x10,(v d)[2]) (List.Mem.tail _ (.head _))
  have h28 := s.slots (0x28,(v d)[3]) (List.Mem.tail _ (List.Mem.tail _ (.head _)))
  have scalarBound : Curve.splitFirst d < domain.n := by
    unfold Curve.splitFirst
    exact Nat.mod_lt _ (by decide +kernel)
  have hbit := highBit_scalar scalarBound
  have block : ∃ (b : Registers) (pre : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l11ca7f,a,m⟩ =
        .call ⟨.l127d50,b,memStore pre (sp fr - 8) (0x11cb3c : BitVec 64)⟩ (callFrame .l11cb3c 0x11cb3c) ∧
      (b[4]'(by decide)).get 64 = sp fr - 8 ∧ (b[7]'(by decide)) = ⟨64,(flag (firstComponent d)).setWidth 64⟩ ∧
      RamWriteFrame m pre (writes fr firstSpans) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i.val]'i.isLt = a[i.val]'i.isLt) ∧
      Locals fr pre (firstSlots d) ∧
      (b[5]'(by decide)) = ⟨64,0x5d576e7357a4501d⟩ ∧
      (b[3]'(by decide)) = ⟨64,0x7fffffffffffffff⟩ ∧
      (b[12]'(by decide)) = (a[12]'(by decide)) ∧
      (b[14]'(by decide)) = (a[14]'(by decide)) ∧
      (b[15]'(by decide)) = (a[15]'(by decide)) := by
    refine ⟨?b, ?pre, ?call, ?stack, ?flag, ?frame, ?args, ?saved, ?keep, ?mem, ?rest⟩
    case call =>
      arithmetic_segment using code_l11ca7f [rsp, r5, r3, r13, r12, h40, h10, h28]
    case stack => rfl
    case flag => exact choiceFlag _ _ hbit
    case frame =>
      try dsimp only
      repeat' refine RamWriteFrame.memStore ?_ _ ?_
      exact RamWriteFrame.refl _ _
      all_goals first
        | exact peerInSlot e (i := 88) (by decide) (by decide)
        | exact peerInSlot e (i := 112) (by decide) (by decide)
        | exact peerInSlot e (i := 80) (by decide) (by decide)
        | exact peerInSlot e (i := 464) (by decide) (by decide)
    case args =>
      rintro ⟨i,hi⟩ hm
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact widths ⟨_,hi⟩ (by decide +revert)
    case saved =>
      rintro ⟨i,hi⟩ hm
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact saved ⟨_,hi⟩ (by decide +revert)
    case keep =>
      rintro ⟨i,hi⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl
    case mem =>
      intro kv hk
      simp only [firstSlots,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp only
      all_goals segment_words [h40,h10,h28]
      all_goals rfl
    case rest => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨b,pre,call,brsp,bflag,frame,args,bsaved,keep,loc,mid,top,b12,b14,b15⟩ := block
  obtain ⟨c,n,path,ctx,cf,under,whole,ck⟩ := finishChoice e s.toContext call brsp bflag
    (by decide) frame (by decide) (by decide) args bsaved keep
  have words := localsAfterChoice e loc (by
    intro kv hk
    simp only [firstSlots,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide) under
  refine ⟨c,n,path,ctx,peerKeepEndo e s.endo whole (by decide),cf,(ck 5 (by decide)).trans mid,
    (ck 3 (by decide)).trans top,(ck 12 (by decide)).trans (b12.trans s.r12),
    (ck 14 (by decide)).trans (b14.trans s.r14),(ck 15 (by decide)).trans (b15.trans s.r15), words⟩

set_option maxHeartbeats 1700000 in
set_option maxRecDepth 8192 in
private theorem secondCompare {fr : Activation} {initial a : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr initial d peer) (s : PeerFirstCompared fr a m d peer) :
    ∃ c n, Reaches .l11cb3c a m .l11cbf4 c n ∧ PeerCompared fr c n d peer := by
  have rsp : (a[4]'(by decide)).get 64 = sp fr := congrArg (Value.get 64) s.atoms.1
  have access := Split.Caller.peerStackAccess e s.frame
  have w : Writable Extracted.programImage m (sp fr) 3256 :=
    (by simpa only [Split.Caller.slot, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      Split.Caller.peerSlotWrite e access (i := 0) (n := 3256) (by decide))
  have push := Split.Caller.peerStackBelowWrite e access (off := 8) (by decide)
  have low := w.readable.low
  have widths := s.widths
  have saved := s.savedWidths
  have r0 := s.firstSign
  have r14 := congrArg (Value.get 64) s.r14
  have r3 := congrArg (Value.get 64) s.top
  have r5 := congrArg (Value.get 64) s.middle
  have h40 := s.slots (0x40,(v d)[1]) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (.head _))))
  have h10 := s.slots (0x10,(v d)[2]) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (.head _)))))
  have h28 := s.slots (0x28,(v d)[3]) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (.head _))))))
  have h58 := s.slots (0x58,(u d)[0]) (.head _)
  have h70 := s.slots (0x70,(u d)[1]) (List.Mem.tail _ (.head _))
  have h50 := s.slots (0x50,(u d)[2]) (List.Mem.tail _ (List.Mem.tail _ (.head _)))
  have scalarBound : Curve.splitSecond d < domain.n := by
    unfold Curve.splitSecond
    exact Nat.mod_lt _ (by decide +kernel)
  have hbit := highBit_scalar scalarBound
  have block : ∃ (b : Registers) (pre : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l11cb3c,a,m⟩ =
        .call ⟨.l127d50,b,memStore pre (sp fr - 8) (0x11cbf4 : BitVec 64)⟩ (callFrame .l11cbf4 0x11cbf4) ∧
      (b[4]'(by decide)).get 64 = sp fr - 8 ∧ (b[7]'(by decide)) = ⟨64,(flag (secondComponent d)).setWidth 64⟩ ∧
      RamWriteFrame m pre (writes fr secondSpans) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i.val]'i.isLt = a[i.val]'i.isLt) ∧
      Locals fr pre (resultSlots d) ∧
      memLoad pre (sp fr + 0x30) 8 = flag (firstComponent d) ∧
      (b[5]'(by decide)) = ⟨64,(v d)[3]⟩ ∧
      (b[12]'(by decide)) = (a[12]'(by decide)) ∧ (b[15]'(by decide)) = (a[15]'(by decide)) := by
    refine ⟨?b, ?pre, ?call, ?stack, ?flag, ?frame, ?args, ?saved, ?keep, ?mem, ?rest⟩
    case call =>
      arithmetic_segment using code_l11cb3c [rsp, r0, r14, r3, r5, h40, h10, h28]
    case stack => rfl
    case flag => exact choiceFlag _ _ hbit
    case frame =>
      try dsimp only
      repeat' refine RamWriteFrame.memStore ?_ _ ?_
      exact RamWriteFrame.refl _ _
      all_goals first
        | exact peerInSlot e (i := 48) (by decide) (by decide)
        | exact peerInSlot e (i := 168) (by decide) (by decide)
        | exact peerInSlot e (i := 464) (by decide) (by decide)
    case args =>
      rintro ⟨i,hi⟩ hm
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact widths ⟨_,hi⟩ (by decide +revert)
    case saved =>
      rintro ⟨i,hi⟩ hm
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact saved ⟨_,hi⟩ (by decide +revert)
    case keep =>
      rintro ⟨i,hi⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl
    case mem =>
      intro kv hk
      simp only [resultSlots,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp only
      all_goals segment_words [h40,h10,h28,h58,h70,h50]
      all_goals rfl
    case rest =>
      refine ⟨?_, rfl,rfl,rfl⟩
      try dsimp only
      segment_words [r0]
      exact (setWidth_get _ (by decide : 8 ≤ 64)).trans r0
  obtain ⟨b,pre,call,brsp,bflag,frame,args,bsaved,keep,loc,sign,b5,b12,b15⟩ := block
  obtain ⟨c,n,path,ctx,cf,under,whole,ck⟩ := finishChoice e s.toContext call brsp bflag
    (by decide) frame (by decide) (by decide) args bsaved keep
  have words := localsAfterChoice e loc (by
    intro kv hk
    simp only [resultSlots,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide) under
  refine ⟨c,n,path,ctx,peerKeepEndo e s.endo whole (by decide),?_,cf,(ck 5 (by decide)).trans b5,
    (ck 12 (by decide)).trans (b12.trans s.r12),(ck 15 (by decide)).trans (b15.trans s.r15),words⟩
  exact (under.memLoad_eq (peerOutside e [] (i := 0x30) (n := 1) (by decide) (by decide))).trans sign


theorem peerCompare {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (s : PeerComparedInput fr a m d peer) :
    ∃ b n, Reaches .l11ca7f a m .l11cbf4 b n ∧ PeerCompared fr b n d peer := by
  obtain ⟨b,m',h,t⟩ := firstCompare entry s
  obtain ⟨c,n,h',v⟩ := secondCompare entry t
  exact ⟨c,n,h.trans h',v⟩
end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
