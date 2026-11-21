import K256.Proofs.Ecdh.Multiply.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Transport

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem peerScratchState {fr : Activation} {initial a b : Registers} {m n : Ram} {d : Nat} {peer : Projective} {l r : Label}
    (entry : PeerCoreEntry fr initial d peer) (s : State l fr a m)
    (src : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (dst : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (delta : RamWriteFrame m n (Bases.writes fr scratchSpans)) (w : ParseSignature.ArgumentWidths b)
    (sv : SavedWidths b) (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    State r fr b n := by
  have within := Bases.peerWithin entry (xs := scratchSpans) (by decide)
  have f := s.frame.trans delta (fun t h => by
    obtain ⟨r,hr,lo,hi⟩ := within _ h
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,.head _,lo,hi⟩)
  have last : Split.Caller.slot fr 3208 = fr.rsp - 48 := by unfold Split.Caller.slot Split.Caller.sp; bv_omega
  refine ⟨frameAtoms s.atoms src dst delta (last ▸ Bases.peerOutside entry scratchSpans (i := 3208) (by decide)
    (by decide)) (by have := entry.room; omega) (entry.loaded_of_frame f) keep,w,sv,f,s.locals.of_frame delta ?_⟩
  intro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    apply Bases.peerOutside entry scratchSpans (i := _) (by decide) (by decide)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
