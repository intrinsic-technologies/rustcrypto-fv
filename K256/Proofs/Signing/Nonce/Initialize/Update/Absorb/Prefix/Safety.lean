import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {fr : Activation} {input : Input}

def area (fr : Activation) (lo hi : Nat) : List MemoryRegion :=
  [⟨(sp fr).toNat + lo, hi - lo⟩]

theorem spNat (env : Environment fr input) : (sp fr).toNat = fr.rsp.toNat - 712 :=
  BitVec.toNat_sub_of_le (by have := env.depth; change 712 ≤ fr.rsp.toNat; omega)

theorem offsetNat (env : Environment fr input) (i : Nat) (h : i ≤ 712) :
    (sp fr + BitVec.ofNat 64 i).toNat = (sp fr).toNat + i := by
  have := spNat env
  have := env.limit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem within {lo hi i n : Nat} (env : Environment fr input) (left : lo ≤ i)
    (right : i + n ≤ hi) (bound : hi ≤ 664) :
    InRegions (area fr lo hi) (sp fr + BitVec.ofNat 64 i) n := by
  refine ⟨_,List.mem_singleton_self _,?_⟩
  change (sp fr).toNat + lo ≤ _ ∧ _ + n ≤ (sp fr).toNat + lo + (hi-lo) ∧ _ + n ≤ 2^64
  rw [offsetNat env _ (by omega)]
  have := spNat env
  have := env.limit
  omega

theorem areaLocal {lo hi : Nat} (env : Environment fr input)
    (h : lo ≤ hi) (bound : hi ≤ 664) : LocalWrites fr (area fr lo hi) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have := env.depth
  have sn := spNat env
  have low : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from env.depth)]
    rfl
  change fr.low.toNat ≤ (sp fr).toNat + lo ∧ (sp fr).toNat + lo + (hi-lo) ≤ _
  omega

theorem stackOutside {lo hi i n : Nat} (env : Environment fr input)
    (bound : i+n ≤ 712) (apart : i+n ≤ lo ∨ hi ≤ i) (ordered : lo ≤ hi) :
    Outside (area fr lo hi) (sp fr + BitVec.ofNat 64 i) n := by
  have addr := offsetNat env i (by omega)
  have := spNat env
  have := env.limit
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change _ ≤ (sp fr).toNat + lo ∨ (sp fr).toNat + lo + (hi-lo) ≤ _
  omega

theorem valueNat (env : Environment fr input) :
    (fr.rdi + 32).toNat = fr.rdi.toNat + 32 := by
  have := env.dataLow
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rdi.toNat + 32 < 2^64; omega)]
  rfl

theorem valueOutside {lo hi i n : Nat} (env : Environment fr input)
    (bound : i+n ≤ 32) (ordered : lo ≤ hi) (stop : hi ≤ 664) :
    Outside (area fr lo hi) (fr.rdi+32+BitVec.ofNat 64 i) n := by
  have localBound := areaLocal env ordered stop _ (List.mem_singleton_self _)
  have := env.dataLow
  have src : (fr.rdi+32+BitVec.ofNat 64 i).toNat = fr.rdi.toNat+32+i := by
    rw [BitVec.toNat_add, valueNat env, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  rcases env.apart with h|h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem stackWritable {m n : Ram} {l : Label} {a : Verify.Core.Registers} {state : State}
    {rs : List MemoryRegion} (env : Environment fr input) (live : Live l fr a m state)
    (writes : RamWriteFrame m n rs) (i len : Nat) (h : i+len ≤ 712) :
    Writable Extracted.programImage n (sp fr + BitVec.ofNat 64 i) len := by
  have sn := spNat env
  have pos := env.depth
  have bot : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le env.depth
  apply ((env.stack.of_frame live.writes).of_frame writes).sub
  all_goals rw [offsetNat env _ (by omega)]; omega

theorem valueReadable {m n : Ram} {l : Label} {a : Verify.Core.Registers} {state : State}
    {rs : List MemoryRegion} (env : Environment fr input) (live : Live l fr a m state)
    (writes : RamWriteFrame m n rs) : Readable n (fr.rdi+32) 32 := by
  apply ((env.writable.readable.of_frame live.writes).of_frame writes).sub
  all_goals rw [valueNat env]; omega


theorem stackStore {lo hi i k : Nat} {m n : Ram} (env : Environment fr input)
    (writes : RamWriteFrame m n (area fr lo hi)) (v : BitVec k)
    (left : lo ≤ i) (right : i + k/8 ≤ hi) (bound : hi ≤ 664) :
    RamWriteFrame m (memStore n (sp fr + BitVec.ofNat 64 i) v) (area fr lo hi) :=
  writes.memStore v (within env left right bound)

theorem storedFrame {lo hi off : Nat} {m n : Ram} (env : Environment fr input)
    (frame : RamWriteFrame m n (area fr lo hi)) (src : BitVec 64)
    (left : lo ≤ off) (right : off + 32 ≤ hi) (bound : hi ≤ 664) :
    RamWriteFrame m (UpdateV.Append.stored n (sp fr + BitVec.ofNat 64 off) src) (area fr lo hi) := by
  have step {t : Ram} (w : RamWriteFrame m t (area fr lo hi)) (i : Nat) (v : BitVec 64)
      (h : i+8 ≤ 32) :
      RamWriteFrame m (memStore t (sp fr + BitVec.ofNat 64 off + BitVec.ofNat 64 i) v) (area fr lo hi) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stackStore env w v (by omega) (by change off+i+8 ≤ hi; omega) bound
  unfold UpdateV.Append.stored
  apply stackStore env _ _ left (by change off+8 ≤ hi; omega) bound
  exact step (step (step frame 24 _ (by decide)) 16 _ (by decide)) 8 _ (by decide)

theorem taggedFrame {lo hi off : Nat} {m n : Ram} (env : Environment fr input)
    (frame : RamWriteFrame m n (area fr lo hi)) (src : BitVec 64) (byte : UInt8)
    (left : lo ≤ off+64) (right : off+128 ≤ hi) (bound : hi ≤ 664) :
    RamWriteFrame m (taggedMemory n (sp fr + BitVec.ofNat 64 off) src byte) (area fr lo hi) := by
  have add (i : Nat) : sp fr + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      sp fr + BitVec.ofNat 64 (off+i) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  unfold taggedMemory
  simp only [show sp fr + BitVec.ofNat 64 off + 64 = _ from add 64,
    show sp fr + BitVec.ofNat 64 off + 127 = _ from add 127,
    show sp fr + BitVec.ofNat 64 off + 96 = _ from add 96]
  have w := storedFrame (off := off+64) env frame src left (by omega) bound
  iterate 3 (apply stackStore env _ _ (by omega) (by change _ + 1 ≤ hi; omega) bound)
  exact w

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
