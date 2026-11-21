import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Serialize.Assemble

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem loadOk_memStore {m : Ram} {a b : BitVec 64} {n w : Nat} {v : BitVec w}
    (h : LoadOk m a n) : LoadOk (memStore m b v) a n :=
  ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi)⟩

theorem storeOk_memStore {code : CodeMap} {m : Ram} {a b pc : BitVec 64} {n w len : Nat}
    {v : BitVec w} (h : StoreOk code m a n pc len) :
    StoreOk code (memStore m b v) a n pc len :=
  ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi), h.tables, h.apart, h.notCode⟩

private theorem inStackRegion {code : CodeMap} {m : Ram} {sp a b : BitVec 64}
    {n len : Nat} (stack : Writable code m (sp - 8) 288)
    (h : (b - (sp - 8)).toNat + len ≤ 288)
    (hab : (a - b).toNat + n ≤ len) : InRegion ⟨b.toNat, len⟩ a n := by
  have zeroSub (x : BitVec 64) : x - (0 : BitVec 64) = x := by bv_omega
  have rb : Readable m b len := stack.readable.of_offsets
    (show b = sp - 8 + (b - (sp - 8)) from by bv_omega) (addr_self (sp - 8))
    (by rw [zeroSub]; exact h)
  change b.toNat ≤ a.toNat ∧ a.toNat + n ≤ b.toNat + len ∧ a.toNat + n ≤ 2^64
  have ha := toNat_of_offsets (n := n) (show a = b + (a - b) from by bv_omega) (addr_self b)
    rb.low (by rw [zeroSub]; exact hab)
  rw [zeroSub] at ha
  have := rb.low
  omega

theorem inStackRegionOffsets {code : CodeMap} {m : Ram} {sp a b c d : BitVec 64}
    {n len : Nat} (stack : Writable code m (sp - 8) 288)
    (ha : a = sp + c) (hb : b = sp + d)
    (h : (d - (0 - 8)).toNat + len ≤ 288) (hab : (c - d).toNat + n ≤ len) :
    InRegion ⟨b.toNat, len⟩ a n := by
  apply inStackRegion stack
  · rwa [hb, addr_sub sp 8, add_sub_add_left']
  · rwa [ha, hb, add_sub_add_left']

theorem stackSlot {code : CodeMap} {m : Ram} {sp a c : BitVec 64} {n : Nat}
    (stack : Writable code m (sp - 8) 288) (ha : a = sp + c)
    (h : (c - (0 - 8)).toNat + n ≤ 288) : Writable code m a n :=
  stack.of_offsets ha (addr_sub sp 8) h

theorem storeOk_inBlock {code : CodeMap} {mem : Ram} {addr base pc : BitVec 64}
    {size len : Nat} {bytes : List UInt8} (hw : Writable code mem addr size)
    (included : ∀ x ∈ codeRange base bytes, x ∈ code)
    (within : (pc - base).toNat + len ≤ bytes.length) :
    StoreOk code mem addr size pc len := by
  have hs := ParseSignature.storeOk_of_codeRange hw included within
  have hp : base + BitVec.ofNat 64 (pc - base).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [hp] at hs

theorem fourWordsAt {mem : Ram} {base : BitVec 64} {v : Vector (BitVec 64) 4}
    (h0 : memLoad mem base 64 = v[0]) (h1 : memLoad mem (base + 8) 64 = v[1])
    (h2 : memLoad mem (base + 16) 64 = v[2]) (h3 : memLoad mem (base + 24) 64 = v[3]) :
    WordsAt mem base 64 v := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using h0
  · exact h1
  · exact h2
  · exact h3

theorem wordsAtOffset {mem : Ram} {sp : BitVec 64} {offset : Nat} {v : Vector (BitVec 64) 4}
    (h : WordsAt mem (sp + BitVec.ofNat 64 offset) 64 v) (i : Nat) (hi : i < 4) :
    memLoad mem (sp + BitVec.ofNat 64 (offset + 8 * i)) 64 = v[i] := by
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc] using h i hi

end K256.Proofs.Sec1.Serialize.Assemble
