import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame
import K256.Proofs.Ecdh.Multiply.Bases.State
import K256.Proofs.Ecdh.Multiply.Split.Memory

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}

theorem peerOutside (e : PeerCoreEntry fr initial d peer) (xs : Spans) {i n : Nat} (bound : i+n ≤ 9500)
    (apart : Separate xs i n) : Outside (writes fr xs) (Split.Caller.slot fr i) n := by
  have pos := e.room
  have high := e.high
  have hs := Split.Caller.peerSpNat e
  have hi := Split.Caller.peerSlotNat e i (by omega)
  change (Split.Caller.slot fr i).toNat = (sp fr).toNat + i at hi
  change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
  refine ⟨by omega, ?_⟩
  intro r hr
  simp only [writes,List.mem_cons,List.mem_map] at hr
  rcases hr with rfl|⟨x,h,rfl⟩
  · right; dsimp only; omega
  · rcases apart x h with h'|h'
    · left; dsimp only; omega
    · right; dsimp only; omega

theorem peerWithin (e : PeerCoreEntry fr initial d peer) {xs : Spans} (bounds : ∀ x ∈ xs, x.1+x.2 ≤ 3208) :
    RegionsWithin (writes fr xs) [fr.region] := by
  have hs := Split.Caller.peerSpNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
  have hl := Split.Caller.peerLowNat e
  have room := e.room
  intro r hr
  refine ⟨_,List.mem_singleton_self fr.region,?_⟩
  simp only [writes,List.mem_cons,List.mem_map] at hr
  rcases hr with rfl|⟨x,h,rfl⟩
  · dsimp only [Activation.region]; omega
  · have := bounds x h
    dsimp only [Activation.region]; omega

theorem peerInSlot (e : PeerCoreEntry fr initial d peer) {xs : Spans} {i size : Nat} (bound : i+size ≤ 9500)
    (covered : ∃ x ∈ xs, x.1 ≤ i ∧ i+size ≤ x.1+x.2) :
    InRegions (writes fr xs) (Split.Caller.slot fr i) size := by
  obtain ⟨x,h,lo,hi⟩ := covered
  have eq := Split.Caller.peerSlotNat e i (by omega)
  change (Split.Caller.slot fr i).toNat = (sp fr).toNat + i at eq
  have hs := Split.Caller.peerSpNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
  have := e.high
  refine ⟨⟨(sp fr).toNat + x.1,x.2⟩,List.mem_cons_of_mem _ (List.mem_map_of_mem (f := _) h),?_⟩
  simp only [InRegion, eq]
  omega

theorem peerInBelow (e : PeerCoreEntry fr initial d peer) (xs : Spans) {i size : Nat}
    (hi : i ≤ 544) (within : size ≤ i) :
    InRegions (writes fr xs) (sp fr - BitVec.ofNat 64 i) size := by
  have eq := Split.Caller.peerStackBelowNat e hi
  change (sp fr - BitVec.ofNat 64 i).toNat = (sp fr).toNat - i at eq
  have hs := Split.Caller.peerSpNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
  have := e.room
  have := e.high
  exact ⟨_,List.mem_cons_self ..,by simp only [InRegion,eq]; omega⟩

theorem peerChildWithin (e : PeerCoreEntry fr initial d peer) {xs : Spans} {i size depth : Nat}
    (stack : depth+8 ≤ 544) (bound : i ≤ 9500)
    (covered : ∃ x ∈ xs, x.1 ≤ i ∧ i+size ≤ x.1+x.2) :
    RegionsWithin [⟨(sp fr-8).toNat-depth,depth⟩,⟨(Split.Caller.slot fr i).toNat,size⟩] (writes fr xs) := by
  have eq := Split.Caller.peerSlotNat e i bound
  change (Split.Caller.slot fr i).toNat = (sp fr).toNat + i at eq
  have push := Split.Caller.peerPushNat e
  change (sp fr-8).toNat = (sp fr).toNat - 8 at push
  have hs := Split.Caller.peerSpNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at hs
  have := e.room
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,by dsimp only; omega,by dsimp only; omega⟩
  · obtain ⟨x,h,lo,hi⟩ := covered
    exact ⟨⟨(sp fr).toNat+x.1,x.2⟩, List.mem_cons_of_mem _ (List.mem_map_of_mem (f := _) h),
      by dsimp only; omega,by dsimp only; omega⟩

theorem Context.peerAdvance {a b : Registers} {m n : Ram} {xs : Spans}
    (s : Context fr a m) (e : PeerCoreEntry fr initial d peer) (frame : RamWriteFrame m n (writes fr xs))
    (bounds : ∀ x ∈ xs, x.1+x.2 ≤ 3208)
    (apart : ∀ i ∈ localOffsets, Separate xs i 8)
    (widths : ParseSignature.ArgumentWidths b) (saved : SavedWidths b)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    Context fr b n := by
  have whole := s.frame.trans frame (peerWithin e bounds)
  have loc : Locals fr n (localValues fr) := by
    apply s.locals.of_frame frame
    intro kv hk
    have member : kv.1.toNat ∈ localOffsets := List.mem_map_of_mem (f := fun p : BitVec 64 × BitVec 64 => p.1.toNat) hk
    have bound : kv.1.toNat + 8 ≤ 9500 := (show ∀ i ∈ localOffsets, i+8 ≤ 9500 by decide) _ member
    simpa only [Split.Caller.slot,Split.Caller.sp,BitVec.ofNat_toNat,BitVec.setWidth_eq,sp] using
      peerOutside e xs bound (apart _ member)
  refine ⟨frameAtoms s.atoms rfl rfl frame ?_ (by have := e.room; omega)
    (e.loaded_of_frame (coreFrame whole)) keep,widths,saved,whole,loc⟩
  have off : Split.Caller.slot fr 3208 = fr.rsp - 48 := by
    unfold Split.Caller.slot Split.Caller.sp
    bv_omega
  rw [← off]
  exact peerOutside e xs (by decide) (fun x h => Or.inr (bounds x h))

theorem peerKeepEndo {m n : Ram} {xs : Spans} (e : PeerCoreEntry fr initial d peer)
    (endo : peerEndoAt fr m peer) (f : RamWriteFrame m n (writes fr xs)) (apart : Separate xs 0x2b0 120) :
    peerEndoAt fr n peer := by
  obtain ⟨p,v,s,h⟩ := endo
  exact ⟨p,v,s.of_frame f (peerOutside e xs (by decide) apart),h⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
