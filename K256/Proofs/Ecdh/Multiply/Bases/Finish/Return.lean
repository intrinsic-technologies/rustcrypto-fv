import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Finish.Return
import K256.Proofs.Ecdh.Multiply.Bases.Finish.Dispatch

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1

private theorem aboveStack {fr : Activation} {initial : Registers} {d i : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (hi : i ≤ 9500) :
    (sp fr).toNat ≤ (Split.Caller.slot fr i).toNat :=
  (Split.Caller.peerSlotNat e i hi).symm ▸ Nat.le_add_right _ _

private theorem selectStackRoom {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) : 544 ≤ (sp fr).toNat := by
  have rsp : (sp fr).toNat = fr.rsp.toNat - 3256 := Split.Caller.peerSpNat e
  have room := e.room
  omega

theorem peerResumeFirstBase {fr : Activation} {initial a b : Registers} {m q : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : PeerNegated fr a m d peer) (h : PeerSelectEntry fr a b m q d peer) :
    ∃ c n, Reaches .l11ccfd a m .l11cf0d c n ∧ c[4] = ⟨64,sp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → c[i] = ⟨64,b[i].get 64⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      ParseSignature.ArgumentWidths c ∧
      (if decide (firstComponent d < 0) then peer.neg else peer).Stored n (sp fr + 0x328) ∧
      RamWriteFrame q n (selectFootprint fr) := by
  have whole := s.frame.trans h.frame (peerWithin e (by decide))
  have access := Split.Caller.peerStackAccess e whole
  have sign : (b[1].get 64).setWidth 8 = if decide (firstComponent d < 0) then 1 else 0 := by
    simpa only [decide_eq_true_eq, flag] using h.firstFlag
  exact Lookup.resumeSelect (l := .l11ccfd) (next := .l11cf0d) (a := a) (b := b) (initial := m)
    (m := q) (sp := sp fr) (ret := 0x11cf0d) (left := sp fr + 3456) (right := sp fr + 0x3a0)
    (dst := sp fr + 0x328) (p := peer) (q := peer.neg)
    (decide (firstComponent d < 0)) h.block
    (get64OfEq h.rsp) (get64OfEq h.src)
    (get64OfEq h.neg) (get64OfEq h.dst) (congrArg Value.width h.dst)
    sign (Split.Caller.peerStackBelowWrite e access (off := 88) (by decide)) (Nat.le_trans (by decide) (selectStackRoom e))
    (by decide) (peerReadable e whole)
    (Split.Caller.peerSlotWrite e access (i := 928) (n := 120) (by decide)).readable
    (Split.Caller.peerSlotWrite e access (i := 808) (n := 120) (by decide))
    (aboveStack e (i := 3456) (by decide)) (aboveStack e (i := 928) (by decide))
    (aboveStack e (i := 808) (by decide)) h.peerStored h.negativeStored

theorem peerSelectFootprintWithin {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) : RegionsWithin (selectFootprint fr) (writes fr selectWrites) := by
  have room := selectStackRoom e
  have below : (sp fr - 88).toNat = (sp fr).toNat - 88 :=
    Split.Caller.peerStackBelowNat e (off := 88) (by decide)
  have dst := Split.Caller.peerSlotNat e 808 (by decide)
  intro r hr
  simp only [selectFootprint, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_,List.mem_cons_self ..,?_⟩
    dsimp only
    rw [below]
    omega
  · exact ⟨⟨(sp fr).toNat+808,120⟩,by simp [writes,selectWrites],
      Nat.le_of_eq dst.symm, Nat.le_of_eq (congrArg (· + 120) dst)⟩

theorem peerKeepSecondMagnitude {fr : Activation} {initial : Registers} {q n : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer)
    (old : WordsAt q (sp fr + 0x290) 64 (scalarWords (secondComponent d).natAbs))
    (frame : RamWriteFrame q n (selectFootprint fr)) :
    WordsAt n (sp fr + 0x290) 64 (scalarWords (secondComponent d).natAbs) := by
  have hi := e.high
  have stack := Split.Caller.peerSpNat e
  have lo88 := Split.Caller.peerStackBelowNat e (off := 88) (by decide)
  have src := Split.Caller.peerSlotNat e 656 (by decide)
  have dst := Split.Caller.peerSlotNat e 808 (by decide)
  apply WordsAt.of_frame old frame (by decide)
  change (sp fr + 656).toNat = (sp fr).toNat + 656 at src
  change (sp fr + 808).toNat = (sp fr).toNat + 808 at dst
  change (sp fr - 88).toNat = (sp fr).toNat - 88 at lo88
  refine ⟨by omega,?_⟩
  intro r hr
  simp only [selectFootprint, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr (by dsimp only; omega)
  · exact Or.inl (by dsimp only; omega)

theorem peerFirstBaseFromSelect {fr : Activation} {n : Ram} {d : Nat} {peer : Projective}
    (valid : peer.valid) (picked : (if decide (firstComponent d < 0) then peer.neg else peer).Stored n (sp fr + 0x328)) :
    ∃ p : Projective, p.valid ∧ p.Stored n (sp fr + 0x328) ∧ p.value = peerFirstBase d peer := by
  by_cases h : firstComponent d < 0
  · simp only [decide_eq_true_eq, h, ite_true] at picked
    exact ⟨peer.neg, Projective.neg_valid valid, picked,
      by simp only [Projective.neg_value, peerFirstBase, Curve.signedBase, h, ite_true]⟩
  · simp only [decide_eq_true_eq, h, ite_false] at picked
    exact ⟨peer, valid, picked,
      by simp only [peerFirstBase, Curve.signedBase, h, ite_false]⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
