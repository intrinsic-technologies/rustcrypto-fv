import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Sites

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev slot (fr : Activation) (i : Nat) := sp fr + BitVec.ofNat 64 i

def Site.dest : Site → Nat
  | .roundFirst | .roundSecond | .mulLambda => 0x128
  | .mulFirst => 0xc10
  | .mulSecond => 0x328
  | .addSecond => 0x418
  | .addFirst => 0x1d0

theorem Site.dest_eq (k : Site) (fr : Activation) (a : Registers) :
    (k.child fr a).rdi = slot fr k.dest := by cases k <;> rfl

def Site.writes (k : Site) (fr : Activation) : List MemoryRegion :=
  [⟨(sp fr).toNat - (8 + k.window),8 + k.window⟩, ⟨(slot fr k.dest).toNat,32⟩]

variable {fr : Activation} {a : Registers} {d : Nat}

theorem spNat (e : CoreEntry fr a d) : (sp fr).toNat = fr.rsp.toNat - 3256 :=
  BitVec.toNat_sub_of_le (by change 3256 ≤ fr.rsp.toNat; have := e.room; omega)

theorem slotNat (e : CoreEntry fr a d) (i : Nat) (hi : i ≤ 9500) :
    (slot fr i).toNat = (sp fr).toNat + i := by
  have := spNat e
  have := e.high
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show (sp fr).toNat + i < 2^64 by omega)]

theorem pushNat (e : CoreEntry fr a d) : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
  BitVec.toNat_sub_of_le (by change 8 ≤ (sp fr).toNat; have := spNat e; have := e.room; omega)

theorem lowNat (e : CoreEntry fr a d) : fr.low.toNat = fr.rsp.toNat - 3800 := by
  rw [e.low]
  exact BitVec.toNat_sub_of_le (by exact e.room)

theorem Site.bounds (k : Site) : k.dest + 32 ≤ 3256 ∧ k.window ≤ 321 ∧ 0 < k.window := by
  cases k <;> decide

theorem Site.within (k : Site) (e : CoreEntry fr a d) :
    RegionsWithin (k.writes fr) [fr.region] := by
  have := k.bounds
  have := spNat e
  have := lowNat e
  have := e.room
  have := slotNat e k.dest (by omega)
  intro r hr
  simp only [Site.writes, List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨_,List.mem_singleton_self fr.region,?_⟩
  rcases hr with rfl|rfl <;> dsimp only [Activation.region] <;> omega

theorem Site.pushFrame (k : Site) (e : CoreEntry fr a d) (m : Ram) :
    RamWriteFrame m (memStore m (sp fr - 8) k.ret) (k.writes fr) := by
  have := k.bounds
  have := spNat e
  have := pushNat e
  have := e.room
  have := e.high
  apply (RamWriteFrame.refl _ _).memStore
  refine ⟨_,List.mem_cons_self ..,?_⟩
  dsimp only [InRegion]
  omega

theorem Site.calleeWithin (k : Site) (e : CoreEntry fr a d) :
    RegionsWithin [⟨(sp fr-8).toNat-k.window,k.window⟩,⟨(slot fr k.dest).toNat,32⟩]
      (k.writes fr) := by
  have := k.bounds
  have := spNat e
  have := pushNat e
  have := e.room
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,by dsimp; omega,by dsimp; omega⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩

theorem Site.outsideSlot (k : Site) (e : CoreEntry fr a d) {i n : Nat} (hi : i + n ≤ 9500)
    (sep : i+n ≤ k.dest ∨ k.dest + 32 ≤ i) : Outside (k.writes fr) (slot fr i) n := by
  have := spNat e
  have := e.high
  have := e.room
  have := k.bounds
  have := slotNat e i (by omega)
  have := slotNat e k.dest (by omega)
  refine ⟨by omega,?_⟩
  intro r hr
  simp only [Site.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> dsimp only <;> omega

theorem Site.keepWords (k : Site) (e : CoreEntry fr a d) {i x : Nat} {m n : Ram}
    (frame : RamWriteFrame m n (k.writes fr)) (words : WordsAt m (slot fr i) 64 (scalarWords x))
    (hi : i + 32 ≤ 9500) (sep : i+32 ≤ k.dest ∨ k.dest+32 ≤ i) :
    WordsAt n (slot fr i) 64 (scalarWords x) := by
  apply WordsAt.of_frame words frame (by decide)
  exact k.outsideSlot e hi sep

theorem Site.keepLocals (k : Site) (e : CoreEntry fr a d) {m n : Ram}
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
  simpa only [slot,BitVec.ofNat_toNat,BitVec.setWidth_eq] using k.outsideSlot e hi apart

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
