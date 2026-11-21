import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Sites
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply.Split.Caller (Site)

theorem bounds (s : Site) : 0 < s.window ∧ s.window ≤ 321 ∧
    destination s + 32 ≤ 648 ∧ (destination s + 32 ≤ 216 ∨ 224 ≤ destination s) ∧
    48 ≤ destination s := by cases s <;> decide

def writes (sp : BitVec 64) (s : Site) : List MemoryRegion :=
  [scratch (frameSp sp) 329, ⟨(slot sp (destination s)).toNat,32⟩]

macro "split_bounds " e:ident : tactic => `(tactic| (
  have room := RoutineEntry.room $e
  have high := (RoutineEntry.returnSlot $e).low
  simp only [scratch,slot,frameSp,BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
    BitVec.reduceToNat,Nat.reducePow,Nat.reduceAdd] at *
  omega))

variable {a : Registers} {m n : Ram} {sp : BitVec 64}

theorem pushFoot (e : RoutineEntry a m sp 0x558) (s : Site) :
    RamWriteFrame n (memStore n (frameSp sp-8) (ret s)) (writes sp s) := by
  apply (RamWriteFrame.refl ..).memStore
  refine ⟨_,.head _,?_⟩
  unfold InRegion
  split_bounds e

theorem callWithin (e : RoutineEntry a m sp 0x558) (s : Site) :
    RegionsWithin [scratch (frameSp sp-8) s.window, ⟨(slot sp (destination s)).toNat,32⟩]
      (writes sp s) := by
  obtain ⟨_,hw,_⟩ := bounds s
  intro r h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨_,.head _,by split_bounds e,by split_bounds e⟩
  · obtain rfl := List.mem_singleton.mp h
    exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩

theorem writesWithin (e : RoutineEntry a m sp 0x558) (s : Site) :
    RegionsWithin (writes sp s) [scratch sp 0x558] := by
  obtain ⟨_,_,hi,_⟩ := bounds s
  intro r h
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl <;> exact ⟨_,.head _,by split_bounds e,by split_bounds e⟩

theorem outsideLocal (e : RoutineEntry a m sp 0x558) (s : Site) (i n : Nat)
    (hi : i+n ≤ 696) (sep : i+n ≤ destination s ∨ destination s+32 ≤ i) :
    Outside (writes sp s) (slot sp i) n := by
  obtain ⟨_,_,destHi,_⟩ := bounds s
  refine ⟨by split_bounds e, fun r hr => ?_⟩
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> split_bounds e

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
