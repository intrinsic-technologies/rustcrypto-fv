import K256.Proofs.Ecdh.Multiply.State
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem peerChildEntry {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (info : FrameInfo) (empty : info.callSlots = [])
    (depth : 0 < info.window ∧ info.window ≤ 536)
    (args : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (rsp : a[4] = ⟨64,sp fr - 8⟩) (df : a[22] = ⟨1,0⟩)
    (mx : a[39] = ⟨32,fr.mxcsr⟩) (ft : a[50] = ⟨16,fr.ftw⟩) (fc : a[51] = ⟨16,fr.fcw⟩)
    {regions : List MemoryRegion} (written : RamWriteFrame fr.original m regions)
    {ret : BitVec 64} (tag : memLoad m (sp fr - 8) 64 = ret) (small : ret.toNat < 2^32) :
    Atom.All Extracted.programImage a m (info.entryAtoms (child fr a m ret)) := by
  have old := entry.atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,win,_,align,_⟩ := old
  change Writable Extracted.programImage fr.original (fr.rsp - 3800) 3800 at win
  change fr.rsp.toNat % 16 = 8 at align
  have depthBound := entry.room
  change 3800 ≤ fr.rsp.toNat at depthBound
  have start : (fr.rsp - 3800).toNat = fr.rsp.toNat - 3800 :=
    BitVec.toNat_sub_of_le (by exact depthBound)
  have top : (sp fr - 8).toNat = fr.rsp.toNat - 3264 := by
    rw [show sp fr - 8 = fr.rsp - 3264 by unfold sp; bv_omega]
    exact BitVec.toNat_sub_of_le (by change 3264 ≤ fr.rsp.toNat; omega)
  have w := win.of_frame written
  have size : (BitVec.ofNat 64 info.window).toNat = info.window :=
    Nat.mod_eq_of_lt (by omega)
  have bot : (sp fr - 8 - BitVec.ofNat 64 info.window).toNat = fr.rsp.toNat - 3264 - info.window := by
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 info.window).toNat ≤ _; rw [size, top]; omega),top,size]
  refine Sample.sampleChildEntry (base := childBase fr a) info empty depth.1 rsp ?keep args ?read tag small ?write ?room ?align
  case keep =>
    have gp (v : Value) (h : v.width = 64) : v = ⟨64,v.get 64⟩ := by
      cases v with
      | mk width bits => cases h; rfl
    intro ⟨i, hi⟩ hm
    simp only [Sample.nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact df
      | exact mx
      | exact ft
      | exact fc
      | exact gp _ (saved 3 (by decide))
      | exact gp _ (saved 5 (by decide))
      | exact gp _ (saved 12 (by decide))
      | exact gp _ (saved 13 (by decide))
      | exact gp _ (saved 14 (by decide))
      | exact gp _ (saved 15 (by decide))
  case read =>
    exact w.readable.sub (by change (fr.rsp - 3800).toNat ≤ (sp fr - 8).toNat; omega)
      (by change (sp fr - 8).toNat + 8 ≤ (fr.rsp - 3800).toNat + 3800; omega)
  case write =>
    exact w.sub (by change (fr.rsp - 3800).toNat ≤ (sp fr - 8 - _).toNat; omega)
      (by change (sp fr - 8 - _).toNat + info.window ≤ (fr.rsp - 3800).toNat + 3800; omega)
  case room =>
    change fr.low.toNat + info.window ≤ (sp fr - 8).toNat
    rw [entry.low, start, top]
    omega
  case align =>
    change (sp fr - 8).toNat % 16 = 8
    omega

end K256.Proofs.Generate.Generator.Multiply.Prepare

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

macro "peer_acc_bounds" " using " e:term : tactic =>
  `(tactic| (
    have room := PeerCoreEntry.room $e
    have high := PeerCoreEntry.high $e
    simp (disch := decide) [writes,pushWrites,roundSp,sp,RegionsWithin,Outside,InRegion,
      coreWrites,Activation.region,PeerCoreEntry.low $e,PeerCoreEntry.tablePtr $e,PeerCoreEntry.digitPtr $e,
      Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,
      BitVec.reduceAdd,BitVec.reduceSub,PeerCoreEntry.stackOffset $e,PeerCoreEntry.aboveStack $e,
      BitVec.reduceToNat] <;> omega))

theorem peerPushFrame {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (m : Ram) (tag : BitVec 64) :
    RamWriteFrame m (memStore m (sp fr - 8) tag) (pushWrites fr) :=
  (RamWriteFrame.refl _ _).memStore tag ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by peer_acc_bounds using entry⟩

theorem peerTransported {fr : Activation} {initial a b : Registers} {d : Nat} {peer : Projective} {m n : Ram}
    {l t : Label} (entry : PeerCoreEntry fr initial d peer) (s : State l fr a m)
    (src : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (dst : Fn11c880.frameAt t fr = Fn11c880.frameAt .l11c9e7 fr)
    (frame : RamWriteFrame m n (writes fr)) (args : ParseSignature.ArgumentWidths b)
    (saved : SavedWidths b) (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    State t fr b n := by
  have full := s.frame.trans frame (by peer_acc_bounds using entry)
  refine ⟨frameAtoms s.atoms src dst frame (by peer_acc_bounds using entry) (by have := entry.room; omega)
    (entry.loaded_of_frame full) keep,args,saved,full,s.locals.of_frame frame ?_⟩
  rintro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> peer_acc_bounds using entry

theorem peerEnter {fr : Activation} {a b initial : Registers} {m : Ram} {d : Nat} {peer : Projective}
    {site target resume : Label} {tag : BitVec 64}
    (entry : PeerCoreEntry fr initial d peer) (s : State site fr a m)
    (layout : Fn11c880.frameAt site fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr site target resume tag a b m) (info : FrameInfo)
    (empty : info.callSlots = []) (depth : 0 < info.window ∧ info.window ≤ 536)
    (small : tag.toNat < 2^32) :
    let n := memStore m (sp fr - 8) tag
    Atom.All Extracted.programImage b n (info.entryAtoms (child fr b n tag)) := by
  intro n
  have h := s.atoms
  rw [layout] at h
  obtain ⟨_,df,mx,ft,fc,_⟩ := h
  exact peerChildEntry entry info empty depth c.widths c.saved c.rsp
    ((c.control 22 (by decide)).trans df) ((c.control 39 (by decide)).trans mx)
    ((c.control 50 (by decide)).trans ft) ((c.control 51 (by decide)).trans fc)
    (s.frame.trans (peerPushFrame entry m tag) (by peer_acc_bounds using entry))
    (memLoad_memStore_same _ _ _ (by decide) (by decide)) small

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
