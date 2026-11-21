import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Core.Serializer

open Prelude X86.Machine X86Proofs K256.Proofs.Refine

private theorem storeByte_eq_write {n : Nat} (m : Ram) (base : BitVec 64)
    (x : BitVec n) (i : Nat) :
    memStore m (base + BitVec.ofNat 64 i) (x.extractLsb' (8 * i) 8) =
      PhysicalMemory.write m (base + BitVec.ofNat 64 i) (storedByte x i) := by
  rw [storedByte_extractLsb']
  unfold memStore
  simp only [show List.range (8 / 8) = [0] from rfl, List.foldl_cons, List.foldl_nil,
    storedByte]
  rw [show base + BitVec.ofNat 64 i + BitVec.ofNat 64 0 = _ from BitVec.add_zero _]

theorem storeBytes_eq_memStore (m : Ram) (base : BitVec 64) (x : BitVec 64) :
    let m0 := memStore m base (x.extractLsb' 0 8)
    let m1 := memStore m0 (base + 1) (x.extractLsb' 8 8)
    let m2 := memStore m1 (base + 2) (x.extractLsb' 16 8)
    let m3 := memStore m2 (base + 3) (x.extractLsb' 24 8)
    let m4 := memStore m3 (base + 4) (x.extractLsb' 32 8)
    let m5 := memStore m4 (base + 5) (x.extractLsb' 40 8)
    let m6 := memStore m5 (base + 6) (x.extractLsb' 48 8)
    let m7 := memStore m6 (base + 7) (x.extractLsb' 56 8)
    m7 = memStore m base x := by
  have h (items : List Nat) (s : Ram) :
      items.foldl (fun mem i =>
        memStore mem (base + BitVec.ofNat 64 i) (x.extractLsb' (8 * i) 8)) s =
      items.foldl (fun mem i =>
        PhysicalMemory.write mem (base + BitVec.ofNat 64 i) (storedByte x i)) s := by
    induction items generalizing s with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons, List.foldl_cons, storeByte_eq_write, ih]
  have eq := h (List.range 8) m
  change _ = memStore m base x at eq
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons,
    List.foldl_nil] at eq
  rw [show base + BitVec.ofNat 64 0 = base from BitVec.add_zero base] at eq
  exact eq

theorem storeWords_wordsAt (m : Ram) (base : BitVec 64) (w : Vector (BitVec 64) 4)
    (low : base.toNat + 32 ≤ 2 ^ 64) :
    let m0 := memStore m base w[0]
    let m1 := memStore m0 (base + 8) w[1]
    let m2 := memStore m1 (base + 16) w[2]
    let m3 := memStore m2 (base + 24) w[3]
    WordsAt m3 base 64 w := by
  let prev : Vector (BitVec 64) 4 := Vector.ofFn fun i => memLoad m (wordAddr base 64 i) 64
  have h : WordsAt m base 64 prev := by
    intro i hi
    simp only [prev, Vector.getElem_ofFn]
  have h0 := WordsAt.write_set h (j := 0) (by decide) w[0] rfl (by decide) (by decide) low
  have h1 := WordsAt.write_set h0 (j := 1) (by decide) w[1] rfl (by decide) (by decide) low
  have h2 := WordsAt.write_set h1 (j := 2) (by decide) w[2] rfl (by decide) (by decide) low
  have writes := WordsAt.write_set h2 (j := 3) (by decide) w[3] rfl (by decide) (by decide) low
  have vals : (((prev.set 0 w[0]).set 1 w[1]).set 2 w[2]).set 3 w[3] = w := by
    apply Vector.ext
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  rw [vals] at writes
  rw [show wordAddr base 64 0 = base from BitVec.add_zero base] at writes
  exact writes

theorem storeWords_frame {o m : Ram} {regions : List MemoryRegion} {base : BitVec 64}
    (w : Vector (BitVec 64) 4) (hf : RamWriteFrame o m regions)
    (dst : InRegions regions base 32) :
    let m0 := memStore m base w[0]
    let m1 := memStore m0 (base + 8) w[1]
    let m2 := memStore m1 (base + 16) w[2]
    let m3 := memStore m2 (base + 24) w[3]
    RamWriteFrame o m3 regions := by
  obtain ⟨r, hr, lower, upper, low⟩ := dst
  have inside (off : Nat) (fits : off + 8 ≤ 32) :
      InRegions regions (base + BitVec.ofNat 64 off) 8 := by
    have addr : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨r, hr, by rw [addr]; omega, by rw [addr]; omega, by rw [addr]; omega⟩
  have first : InRegions regions base 8 := by
    have h := inside 0 (by decide)
    rwa [show base + BitVec.ofNat 64 0 = base from BitVec.add_zero base] at h
  have h0 := hf.memStore w[0] first
  have h1 := h0.memStore w[1] (inside 8 (by decide))
  have h2 := h1.memStore w[2] (inside 16 (by decide))
  exact h2.memStore w[3] (inside 24 (by decide))

end K256.Proofs.Verify.Core.Serializer
