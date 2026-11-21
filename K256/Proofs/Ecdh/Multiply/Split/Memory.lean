import K256.Proofs.Ecdh.Multiply.State
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Arguments

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

variable {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}

theorem peerSpNat (e : PeerCoreEntry fr a d peer) : (sp fr).toNat = fr.rsp.toNat - 3256 :=
  e.stackOffset 3256 (by decide)

theorem peerSlotNat (e : PeerCoreEntry fr a d peer) (i : Nat) (hi : i ≤ 9500) :
    (slot fr i).toNat = (sp fr).toNat + i := by
  have := peerSpNat e
  have := e.high
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show (sp fr).toNat + i < 2^64 by omega)]

theorem peerPushNat (e : PeerCoreEntry fr a d peer) : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
  BitVec.toNat_sub_of_le (by change 8 ≤ (sp fr).toNat; have := peerSpNat e; have := e.room; omega)

theorem peerLowNat (e : PeerCoreEntry fr a d peer) : fr.low.toNat = fr.rsp.toNat - 3800 := by
  rw [e.low]
  exact e.stackOffset 3800 (by decide)

theorem Site.peerWithin (k : Site) (e : PeerCoreEntry fr a d peer) :
    RegionsWithin (k.writes fr) [fr.region] := by
  have := k.bounds
  have := peerSpNat e
  have := peerLowNat e
  have := e.room
  have := peerSlotNat e k.dest (by omega)
  intro r hr
  simp only [Site.writes, List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨_,List.mem_singleton_self fr.region,?_⟩
  rcases hr with rfl|rfl <;> dsimp only [Activation.region] <;> omega

theorem Site.peerPushFrame (k : Site) (e : PeerCoreEntry fr a d peer) (m : Ram) :
    RamWriteFrame m (memStore m (sp fr - 8) k.ret) (k.writes fr) := by
  have := k.bounds
  have := peerSpNat e
  have := peerPushNat e
  have := e.room
  have := e.high
  apply (RamWriteFrame.refl _ _).memStore
  refine ⟨_,List.mem_cons_self ..,?_⟩
  dsimp only [InRegion]
  omega

theorem Site.peerCalleeWithin (k : Site) (e : PeerCoreEntry fr a d peer) :
    RegionsWithin [⟨(sp fr-8).toNat-k.window,k.window⟩,⟨(slot fr k.dest).toNat,32⟩]
      (k.writes fr) := by
  have := k.bounds
  have := peerSpNat e
  have := peerPushNat e
  have := e.room
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,by dsimp; omega,by dsimp; omega⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩

theorem Site.peerOutsideSlot (k : Site) (e : PeerCoreEntry fr a d peer) {i n : Nat} (hi : i + n ≤ 9500)
    (sep : i+n ≤ k.dest ∨ k.dest + 32 ≤ i) : Outside (k.writes fr) (slot fr i) n := by
  have := peerSpNat e
  have := e.high
  have := e.room
  have := k.bounds
  have := peerSlotNat e i (by omega)
  have := peerSlotNat e k.dest (by omega)
  refine ⟨by omega,?_⟩
  intro r hr
  simp only [Site.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> dsimp only <;> omega

theorem Site.peerKeepWords (k : Site) (e : PeerCoreEntry fr a d peer) {i x : Nat} {m n : Ram}
    (frame : RamWriteFrame m n (k.writes fr)) (words : WordsAt m (slot fr i) 64 (scalarWords x))
    (hi : i + 32 ≤ 9500) (sep : i+32 ≤ k.dest ∨ k.dest+32 ≤ i) :
    WordsAt n (slot fr i) 64 (scalarWords x) := by
  apply WordsAt.of_frame words frame (by decide)
  exact k.peerOutsideSlot e hi sep

theorem Site.peerKeepLocals (k : Site) (e : PeerCoreEntry fr a d peer) {m n : Ram}
    (frame : RamWriteFrame m n (k.writes fr)) (words : LocalsAt fr m) : LocalsAt fr n := by
  intro kv hk
  have hs : kv.1.toNat ∈ ([8,56,96,104,136,176,192,216,240,256,416,448,584,3208,
      3216,3224,3232,3240,3248] : List Nat) := by
    exact
      (List.mem_map_of_mem (f := fun p : BitVec 64 × BitVec 64 => p.1.toNat) hk)
  have sep (i : Nat) (h : i ∈ ([8,56,96,104,136,176,192,216,240,256,416,448,584,3208,
      3216,3224,3232,3240,3248] : List Nat)) :
      i+8 ≤ 9500 ∧ (i+8 ≤ k.dest ∨ k.dest+32 ≤ i) := by
    have checked : ∀ j ∈ ([8,56,96,104,136,176,192,216,240,256,416,448,584,3208,
      3216,3224,3232,3240,3248] : List Nat), j+8 ≤ 9500 ∧ (j+8 ≤ k.dest ∨ k.dest+32 ≤ j) := by
      cases k <;> decide +kernel
    exact checked i h
  obtain ⟨hi, apart⟩ := sep _ hs
  apply (frame.memLoad_eq _).trans (words kv hk)
  simpa only [slot,BitVec.ofNat_toNat,BitVec.setWidth_eq] using k.peerOutsideSlot e hi apart

theorem peerStackAccess {m : Ram}
    (e : PeerCoreEntry fr a d peer) (f : RamWriteFrame fr.original m [fr.region]) : StackAccess fr m := by
  have atoms := e.atoms
  simp only [Fn11c880.frameAt,Fn11c880.frameAtG1,Atom.All,Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,stack,_,align,_⟩ := atoms
  exact ⟨stack.of_frame f,align⟩

variable {m : Ram}

theorem peerSlotWrite (e : PeerCoreEntry fr a d peer) (s : StackAccess fr m) {i n : Nat} (hi : i+n ≤ 3256) :
    Writable Extracted.programImage m (slot fr i) n := by
  have := e.room
  have := peerSpNat e
  have := peerSlotNat e i (by omega)
  have := peerLowNat e
  have w := s.stack
  rw [← e.low] at w
  exact w.sub (by omega) (by omega)

theorem peerStackBelowNat (e : PeerCoreEntry fr a d peer) {off : Nat} (h : off ≤ 544) :
    (sp fr - BitVec.ofNat 64 off).toNat = (sp fr).toNat - off := by
  have := peerSpNat e
  have := e.room
  rw [BitVec.toNat_sub_of_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  change (BitVec.ofNat 64 off).toNat ≤ (sp fr).toNat
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem peerStackBelowWrite (e : PeerCoreEntry fr a d peer) (s : StackAccess fr m) {off : Nat} (h : off ≤ 544) :
    Writable Extracted.programImage m (sp fr - BitVec.ofNat 64 off) off := by
  have := peerSpNat e
  have := peerStackBelowNat e h
  have := peerLowNat e
  have := e.room
  have w := s.stack
  rw [← e.low] at w
  exact w.sub (by omega) (by omega)

theorem peerScalarAddress (e : PeerCoreEntry fr a d peer) : fr.rsi + 120 = slot fr 3576 := by
  rw [e.pairPtr]
  unfold slot sp
  bv_omega

theorem Site.peerTransfer (k : Site) {d : Nat} {peer : Projective} {fr : Activation} {a : Registers} (e : PeerCoreEntry fr a d peer)
    {m n : Ram} (frame : RamWriteFrame m n (k.writes fr))
    (before : ScalarsAt fr m (k.before d)) : ScalarsAt fr n (k.before d) := by
  intro kv h
  obtain ⟨hi,apart⟩ := k.before_apart d h
  exact k.peerKeepWords e frame (before kv h) (by omega) apart

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
