import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine K256.Proofs.Lift

theorem input_byte_of_frame {old m : Ram} {regions : List MemoryRegion}
    {src : BitVec 64} {i : Nat} (h : RamWriteFrame old m regions) (apart : Outside regions src 33)
    (hi : i < 33) :
    memByte m (src + BitVec.ofNat 64 i) = memByte old (src + BitVec.ofNat 64 i) := by
  have low := apart.1
  have addr : (src + BitVec.ofNat 64 i).toNat = src.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [memByte, PhysicalMemory.read]
  congr 1
  refine h.outside _ ⟨by omega, fun r hr => ?_⟩
  rcases apart.2 r hr with l | r <;> omega

inductive ByteOrigin where
  | initial (offset : Nat)
  | input (offset : Nat)
  | accumulator (offset : Nat)
  | zero
  deriving DecidableEq

inductive StackImage where
  | original
  | zero (prior : StackImage) (dst : Fin 264) (wide : Bool)
  | input (prior source : StackImage) (dst : Fin 264) (src : Fin 33) (wide : Bool) (fits : src.val + (if wide then 8 else 4) ≤ 33)
  | copy (prior source : StackImage) (dst src : Fin 264) (wide : Bool)
  | accumulator (prior : StackImage) (dst : Fin 264)

namespace StackImage

private def width (wide : Bool) : Nat := if wide then 64 else 32

def memory (sp src : BitVec 64) (m : Ram) (acc : BitVec 32) : StackImage → Ram
  | .original => m
  | .zero p d w => memStore (p.memory sp src m acc) (sp + BitVec.ofNat 64 d) (0 : BitVec (width w))
  | .input p q d s w _ => memStore (p.memory sp src m acc) (sp + BitVec.ofNat 64 d)
      (memLoad (q.memory sp src m acc) (src + BitVec.ofNat 64 s) (width w))
  | .copy p q d s w => memStore (p.memory sp src m acc) (sp + BitVec.ofNat 64 d)
      (memLoad (q.memory sp src m acc) (sp + BitVec.ofNat 64 s) (width w))
  | .accumulator p d => memStore (p.memory sp src m acc) (sp + BitVec.ofNat 64 d) acc

private def overwritten (dst w i : Nat) : Prop := dst ≤ i ∧ i < dst + w / 8
private instance {dst w i : Nat} : Decidable (overwritten dst w i) := inferInstanceAs (Decidable (_ ∧ _))

def origin : StackImage → Nat → ByteOrigin
  | .original, i => .initial i
  | .zero p d w, i => if overwritten d (width w) i then .zero else p.origin i
  | .input p _ d s w _, i => if overwritten d (width w) i then .input (s + (i - d)) else p.origin i
  | .copy p q d s w, i => if overwritten d (width w) i then q.origin (s + (i - d)) else p.origin i
  | .accumulator p d, i => if overwritten d 32 i then .accumulator (i - d) else p.origin i

def byte (sp src : BitVec 64) (m : Ram) (acc : BitVec 32) : ByteOrigin → UInt8
  | .initial i => memByte m (sp + BitVec.ofNat 64 i)
  | .input i => memByte m (src + BitVec.ofNat 64 i)
  | .accumulator i => storedByte acc i
  | .zero => 0

private theorem byte_store {p : Ram} {sp : BitVec 64} {n : Nat} {v : BitVec n}
    {d : Fin 264} {i : Nat} (hi : i < 512) (hn : n ≤ 64) :
    memByte (memStore p (sp + BitVec.ofNat 64 d) v) (sp + BitVec.ofNat 64 i) =
      if overwritten d n i then storedByte v (i - d) else memByte p (sp + BitVec.ofNat 64 i) := by
  split
  next h =>
    obtain ⟨hle, hlt⟩ := h
    have hj : i - d.val < n / 8 := by omega
    have ha : sp + BitVec.ofNat 64 i =
        sp + BitVec.ofNat 64 d + BitVec.ofNat 64 (i - d) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hle]
    rw [ha, memByte]
    simp only [PhysicalMemory.read]
    rw [memStore_getElem?_self_of_le _ _ _ (by omega) _ hj]
    rfl
  next h =>
    have ha : ∀ j, j < n / 8 →
        sp + BitVec.ofNat 64 d + BitVec.ofNat 64 j ≠ sp + BitVec.ofNat 64 i := by
      intro j hj he
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
      have eq := add_ofNat_inj sp (i := i) (j := d.val + j) (by omega)
        (by have := d.isLt; omega) he
      exact h ⟨by omega, by omega⟩
    change ((memStore _ _ _)[sp + BitVec.ofNat 64 i]?).getD 0 = _
    rw [memStore_getElem?_of_ne _ _ _ _ ha]
    rfl

private theorem width_le (w : Bool) : width w ≤ 64 := by cases w <;> decide

def endOffset : StackImage → Nat
  | .original => 0
  | .zero p d w => max p.endOffset (d + width w / 8)
  | .input p q d _ w _
  | .copy p q d _ w => max (max p.endOffset q.endOffset) (d + width w / 8)
  | .accumulator p d => max p.endOffset (d + 4)

private theorem singleton_in {sp : BitVec 64} {bound n : Nat} (d : Fin 264)
    (h : d.val + n ≤ bound) (low : sp.toNat + bound < 2^64) :
    InRegions [⟨sp.toNat, bound⟩] (sp + BitVec.ofNat 64 d) n := by
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have he : (sp + BitVec.ofNat 64 d.val).toNat = sp.toNat + d.val := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := d.isLt; omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [InRegion, he]
  omega

theorem frame (img : StackImage) (sp src : BitVec 64) (m : Ram) (acc : BitVec 32)
    {bound : Nat} (hbound : img.endOffset ≤ bound) (low : sp.toNat + bound < 2^64) :
    RamWriteFrame m (img.memory sp src m acc) [⟨sp.toNat, bound⟩] := by
  induction img with
  | original => exact .refl _ _
  | zero p d w ih =>
    obtain ⟨hp, hd⟩ := Nat.max_le.mp hbound
    exact (ih hp).memStore _ (singleton_in d hd low)
  | input p _ d _ w _ ih _
  | copy p _ d _ w ih _ =>
    obtain ⟨hp, hd⟩ := Nat.max_le.mp hbound
    exact (ih (Nat.max_le.mp hp).1).memStore _ (singleton_in d hd low)
  | accumulator p d ih =>
    obtain ⟨hp, hd⟩ := Nat.max_le.mp hbound
    exact (ih hp).memStore _ (singleton_in d hd low)

theorem byte_origin (img : StackImage) (sp src : BitVec 64) (m : Ram) (acc : BitVec 32)
    {bound : Nat} (limit : img.endOffset ≤ bound) (low : sp.toNat + bound < 2^64)
    (outside : Outside [⟨sp.toNat, bound⟩] src 33)
    (i : Nat) (hi : i < 512) :
    memByte (img.memory sp src m acc) (sp + BitVec.ofNat 64 i) =
      byte sp src m acc (img.origin i) := by
  induction img generalizing i with
  | original => rfl
  | zero prior dst wide ih =>
    obtain ⟨hp, _⟩ := Nat.max_le.mp limit
    rw [memory, byte_store hi (width_le wide), origin]
    split
    · cases wide <;> simp [width, storedByte, byte]
    · exact ih hp i hi
  | input prior copied dst source wide fits ihPrior _ =>
    obtain ⟨hpq, _⟩ := Nat.max_le.mp limit
    obtain ⟨hp, hq⟩ := Nat.max_le.mp hpq
    rw [memory, byte_store hi (width_le wide), origin]
    split
    next h =>
      obtain ⟨hle, hlt⟩ := h
      have hbyte : i - dst.val < width wide / 8 := by omega
      rw [storedByte_memLoad _ _ _ hbyte]
      simp only [byte, BitVec.add_assoc, ← BitVec.ofNat_add]
      apply input_byte_of_frame (copied.frame sp src m acc hq low) outside
      have wf : width wide / 8 = (if wide then 8 else 4) := by cases wide <;> decide
      omega
    · exact ihPrior hp i hi
  | copy prior copied dst source wide ihPrior ihFrom =>
    obtain ⟨hpq, _⟩ := Nat.max_le.mp limit
    obtain ⟨hp, hq⟩ := Nat.max_le.mp hpq
    rw [memory, byte_store hi (width_le wide), origin]
    split
    next h =>
      obtain ⟨hle, hlt⟩ := h
      have hw := width_le wide
      rw [storedByte_memLoad _ _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ihFrom hq _ (by have := source.isLt; omega)
    · exact ihPrior hp i hi
  | accumulator prior dst ih =>
    obtain ⟨hp, _⟩ := Nat.max_le.mp limit
    rw [memory, byte_store hi (by decide), origin]
    split
    · rfl
    · exact ih hp i hi

end StackImage

end K256.Proofs.Ecdh.Decode.Packing
