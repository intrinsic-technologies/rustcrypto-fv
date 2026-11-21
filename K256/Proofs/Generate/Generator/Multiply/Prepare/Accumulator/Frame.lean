import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.CallBlocks
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def writes (fr : Activation) : List MemoryRegion :=
  [⟨(sp fr - 544).toNat,544⟩,⟨(sp fr + 8).toNat,8⟩,⟨(sp fr + 56).toNat,8⟩,
   ⟨(sp fr + 296).toNat,120⟩,⟨(sp fr + 464).toNat,120⟩,⟨(sp fr + 1168).toNat,1920⟩]

def pushWrites (fr : Activation) : List MemoryRegion := [⟨(sp fr - 8).toNat,8⟩]

macro "acc_bounds" " using " e:term : tactic =>
  `(tactic| (
    have room := CoreEntry.room $e
    have high := CoreEntry.high $e
    simp (disch := decide) [writes,pushWrites,roundSp,sp,RegionsWithin,Outside,InRegion,
      coreWrites,Activation.region,CoreEntry.low $e,CoreEntry.tablePtr $e,CoreEntry.digitPtr $e,
      Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,
      BitVec.reduceAdd,BitVec.reduceSub,CoreEntry.stackOffset $e,CoreEntry.aboveStack $e,
      BitVec.reduceToNat] <;> omega))

theorem pushFrame {fr : Activation} {initial : Registers} {d : Nat}
    (entry : CoreEntry fr initial d) (m : Ram) (tag : BitVec 64) :
    RamWriteFrame m (memStore m (sp fr - 8) tag) (pushWrites fr) :=
  (RamWriteFrame.refl _ _).memStore tag ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by acc_bounds using entry⟩

theorem transported {fr : Activation} {initial a b : Registers} {d : Nat} {m n : Ram}
    {l t : Label} (entry : CoreEntry fr initial d) (s : State l fr a m)
    (src : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (dst : Fn11c880.frameAt t fr = Fn11c880.frameAt .l11c9e7 fr)
    (frame : RamWriteFrame m n (writes fr)) (args : ParseSignature.ArgumentWidths b)
    (saved : SavedWidths b) (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    State t fr b n := by
  have full := s.frame.trans frame (by acc_bounds using entry)
  refine ⟨frameAtoms s.atoms src dst frame (by acc_bounds using entry) (by have := entry.room; omega)
    (entry.loaded_of_frame full) keep,args,saved,full,s.locals.of_frame frame ?_⟩
  rintro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> acc_bounds using entry

theorem currentStack {fr : Activation} {a : Registers} {m : Ram} {l : Label}
    (s : State l fr a m) (src : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr) :
    a[4] = ⟨64,sp fr⟩ ∧ a[22] = ⟨1,0⟩ ∧ Writable Extracted.programImage m (fr.rsp - 3800) 3800 := by
  have h := s.atoms
  rw [src] at h
  exact ⟨h.1,h.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem enter {fr : Activation} {a b initial : Registers} {m : Ram} {d : Nat}
    {site target resume : Label} {tag : BitVec 64}
    (entry : CoreEntry fr initial d) (s : State site fr a m)
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
  exact childEntry entry info empty depth c.widths c.saved c.rsp
    ((c.control 22 (by decide)).trans df) ((c.control 39 (by decide)).trans mx)
    ((c.control 50 (by decide)).trans ft) ((c.control 51 (by decide)).trans fc)
    (s.frame.trans (pushFrame entry m tag) (by acc_bounds using entry))
    (memLoad_memStore_same _ _ _ (by decide) (by decide)) small

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
