import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.FinishCopy
import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev scratchSpans : Bases.Spans := [(296,120),(464,120),(808,120),(1048,2160)]

theorem spansWithin (fr : Activation) {xs ys : Bases.Spans}
    (bounds : ∀ x ∈ xs, ∃ y ∈ ys, y.1 ≤ x.1 ∧ x.1+x.2 ≤ y.1+y.2) :
    RegionsWithin (Bases.writes fr xs) (Bases.writes fr ys) := by
  intro r hr
  simp only [Bases.writes,List.mem_cons,List.mem_map] at hr
  rcases hr with rfl|⟨x,h,rfl⟩
  · exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩
  · obtain ⟨y,hy,lo,hi⟩ := bounds _ h
    refine ⟨_,.tail _ (List.mem_map_of_mem (f := _) hy),?_⟩
    dsimp only
    omega

theorem inductionWithin (first : Bool) (fr : Activation) :
    RegionsWithin (tableWrites (sp fr) first) (Bases.writes fr scratchSpans) := by
  cases first
  · exact spansWithin fr (xs := [(1048,120),(1168,960),(296,120),(464,120)]) (by decide)
  · exact spansWithin fr (xs := [(1048,120),(2128,960),(296,120),(464,120)]) (by decide)

theorem finishWithin (first : Bool) (fr : Activation) :
    RegionsWithin [⟨(sp fr).toNat+1048,120⟩,⟨(sp fr).toNat+entryOff first 7,120⟩]
      (Bases.writes fr scratchSpans) := by
  intro r hr
  refine ⟨⟨(sp fr).toNat+1048,2160⟩,by simp [Bases.writes,scratchSpans],?_⟩
  rcases List.mem_cons.mp hr with rfl|hr
  · exact ⟨Nat.le_refl _,by dsimp only; omega⟩
  · obtain rfl := List.mem_singleton.mp hr
    cases first <;> dsimp [entryOff] <;> omega

theorem scratchState {fr : Activation} {initial a b : Registers} {m n : Ram} {d : Nat} {l r : Label}
    (entry : CoreEntry fr initial d) (s : State l fr a m)
    (src : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (dst : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (delta : RamWriteFrame m n (Bases.writes fr scratchSpans)) (w : ParseSignature.ArgumentWidths b)
    (sv : SavedWidths b) (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    State r fr b n := by
  have within := Bases.within entry (xs := scratchSpans) (by decide)
  have f := s.frame.trans delta (fun t h => by
    obtain ⟨r,hr,lo,hi⟩ := within _ h
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,.head _,lo,hi⟩)
  have last : Split.Caller.slot fr 3208 = fr.rsp - 48 := by unfold Split.Caller.slot Split.Caller.sp; bv_omega
  refine ⟨frameAtoms s.atoms src dst delta (last ▸ Bases.outside entry scratchSpans (i := 3208) (by decide)
    (by decide)) (by have := entry.room; omega) (entry.loaded_of_frame f) keep,w,sv,f,s.locals.of_frame delta ?_⟩
  intro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    apply Bases.outside entry scratchSpans (i := _) (by decide) (by decide)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
