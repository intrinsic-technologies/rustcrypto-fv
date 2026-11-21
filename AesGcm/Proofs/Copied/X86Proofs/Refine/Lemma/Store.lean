import AesGcm.Proofs.Copied.X86Proofs.Refine.Store
import X86Proofs.Program.Compose

namespace X86Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift Prelude

theorem RangeApart.of_diff {a b : BitVec 64} {n k : Nat}
    (h : n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat) : RangeApart a n b k := by
  intro i hi j hj he
  have he' := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
  obtain ⟨h1, h2⟩ := h
  simp only [BitVec.toNat_sub] at h1 h2
  have := a.isLt
  have := b.isLt
  have : (b - a).toNat < 2 ^ 64 := (b - a).isLt
  omega

theorem RangeApart.right_sub {a b : BitVec 64} {n m : Nat} (h : RangeApart a n b m) {off m' : Nat}
    (hoff : off + m' ≤ m) : RangeApart a n (b + BitVec.ofNat 64 off) m' := by
  intro i hi j hj he
  refine h i hi (off + j) (by omega) ?_
  rw [he, BitVec.add_assoc, BitVec.ofNat_add]

theorem sub_sub_sub_left (x c d : BitVec 64) : x - c - (x - d) = d - c := by bv_omega
theorem add_sub_add_left' (x c d : BitVec 64) : x + c - (x + d) = c - d := by bv_omega
theorem add_sub_sub_left (x c d : BitVec 64) : x + c - (x - d) = c + d := by bv_omega
theorem sub_sub_add_left (x c d : BitVec 64) : x - c - (x + d) = 0 - c - d := by bv_omega
theorem sub_sub_self_left (x d : BitVec 64) : x - (x - d) = d := by bv_omega
theorem sub_add_self_left (x d : BitVec 64) : x - (x + d) = 0 - d := by bv_omega
theorem add_sub_self_right (x c : BitVec 64) : x + c - x = c := by bv_omega
theorem sub_sub_self_right (x c : BitVec 64) : x - c - x = 0 - c := by bv_omega

theorem addr_self (a : BitVec 64) : a = a + 0 := (BitVec.add_zero a).symm
theorem addr_sub (x c : BitVec 64) : x - c = x + (0 - c) := by bv_omega
theorem addr_lit (c : BitVec 64) : c = 0 + c := (BitVec.zero_add c).symm

theorem addr_eq_of_offsets {a b x c d : BitVec 64} (ha : a = x + c) (hb : b = x + d) (h : c = d) :
    a = b := by
  subst ha hb h
  rfl

theorem addr_add_of_offsets {a b x c d e : BitVec 64} (ha : a = x + c) (hb : b = x + d)
    (h : d - c = e) : b = a + e := by
  subst ha hb h
  bv_omega

theorem RangeApart.of_offsets {a b x c d : BitVec 64} {n k : Nat} (ha : a = x + c) (hb : b = x + d)
    (h : n ≤ (d - c).toNat ∧ k ≤ (c - d).toNat) : RangeApart a n b k := by
  subst ha hb
  exact RangeApart.of_diff (by rwa [add_sub_add_left', add_sub_add_left'])

theorem toNat_of_offsets {a r x c d : BitVec 64} {n len : Nat} (ha : a = x + c) (hr : r = x + d)
    (hlow : r.toNat + len ≤ 2 ^ 32) (h : (c - d).toNat + n ≤ len) :
    a.toNat = r.toNat + (c - d).toNat := by
  have he : a = r + (c - d) := by subst ha hr; bv_omega
  rw [he, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem RangeApart.of_regions {a b r s x y c d e f : BitVec 64} {n k len₁ len₂ : Nat}
    (ha : a = x + c) (hr : r = x + d) (hb : b = y + e) (hs : s = y + f)
    (hlr : r.toNat + len₁ ≤ 2 ^ 32) (hls : s.toNat + len₂ ≤ 2 ^ 32)
    (hap : r.toNat + len₁ ≤ s.toNat ∨ s.toNat + len₂ ≤ r.toNat)
    (hin : (c - d).toNat + n ≤ len₁ ∧ (e - f).toNat + k ≤ len₂) : RangeApart a n b k := by
  have h1 := toNat_of_offsets ha hr hlr hin.1
  have h2 := toNat_of_offsets hb hs hls hin.2
  exact RangeApart.of_toNat (by omega) (by omega) (by omega)

attribute [store_norm] memLoad_memStore_same memLoad_memStore_of_rangeApart

theorem memLoad_memStore_eq (mem : Ram) {a b : BitVec 64} {n : Nat} (v : BitVec n) (hab : a = b)
    (h8 : n % 8 = 0) (h128 : n ≤ 128) : memLoad (memStore mem a v) b n = v := by
  subst hab
  exact memLoad_memStore_same mem a v h8 h128

theorem memLoad_memStore_within (mem : Ram) {a b : BitVec 64} {n : Nat} (v : BitVec n) (w off : Nat)
    (hb : b = a + BitVec.ofNat 64 off) (hw : w % 8 = 0) (hin : off + w / 8 ≤ n / 8)
    (h128 : n ≤ 128) : memLoad (memStore mem a v) b w = v.extractLsb' (8 * off) w := by
  subst hb
  apply memLoad_eq_of_memByte hw
  intro i hi
  have hbyte : memByte (memStore mem a v) (a + BitVec.ofNat 64 off + BitVec.ofNat 64 i) =
      storedByte v (off + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, memByte]
    simp only [PhysicalMemory.read]
    rw [memStore_getElem?_self_of_le mem a v (by omega) (off + i) (by omega)]
    rfl
  rw [hbyte, storedByte_extractLsb' v (off + i),
    storedByte_extractLsb' (v.extractLsb' (8 * off) w) i]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb']
  simp [hk, show 8 * i + k < w by omega, Nat.mul_add, Nat.add_assoc]

theorem extractLsb'_memLoad (mem : Ram) (a : BitVec 64) {n : Nat} (s w : Nat)
    (hs : s % 8 = 0) (hw : w % 8 = 0) (h : s + w ≤ n) :
    (memLoad mem a n).extractLsb' s w = memLoad mem (a + BitVec.ofNat 64 (s / 8)) w := by
  symm
  apply memLoad_eq_of_memByte hw
  intro i hi
  have hx : (memLoad mem a n).extractLsb' (8 * (s / 8 + i)) 8 =
      ((memLoad mem a n).extractLsb' s w).extractLsb' (8 * i) 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_extractLsb']
    simp [hk, show 8 * i + k < w by omega, show 8 * (s / 8 + i) + k = s + (8 * i + k) by omega]
  rw [storedByte_extractLsb', ← hx, ← storedByte_extractLsb',
    storedByte_memLoad mem a (s / 8 + i) (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

theorem RamWriteFrame.refl (m : Ram) (regions : List MemoryRegion) : RamWriteFrame m m regions :=
  ⟨fun _ _ => rfl, fun _ h => h⟩

private theorem ne_of_inRegion {r : MemoryRegion} {a x : BitVec 64} {n i : Nat}
    (hin : InRegion r a n) (hi : i < n) (hx : x.toNat + 1 ≤ r.start ∨ r.start + r.size ≤ x.toNat) :
    a + BitVec.ofNat 64 i ≠ x := by
  intro he
  have he' := congrArg BitVec.toNat he
  obtain ⟨h1, h2, h3⟩ := hin
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)] at he'
  omega

theorem RamWriteFrame.memStore {o m : Ram} {regions : List MemoryRegion}
    (h : RamWriteFrame o m regions) {a : BitVec 64} {n : Nat} (v : BitVec n)
    (hin : InRegions regions a (n / 8)) :
    RamWriteFrame o (memStore m a v) regions where
  outside x hx := by
    obtain ⟨r, hr, hin⟩ := hin
    rw [memStore_getElem?_of_ne m a v x fun i hi => ne_of_inRegion hin hi (hx.2 r hr)]
    exact h.outside x hx
  present x hx := memStore_isSome m a v x (h.present x hx)

theorem RamWriteFrame.trans {o m m' : Ram} {regions regions' : List MemoryRegion}
    (h₁ : RamWriteFrame o m regions) (h₂ : RamWriteFrame m m' regions')
    (hw : RegionsWithin regions' regions) : RamWriteFrame o m' regions where
  outside x hx := by
    rw [h₂.outside x ⟨hx.1, fun r hr => ?_⟩, h₁.outside x hx]
    obtain ⟨r', hr', h1, h2⟩ := hw r hr
    rcases hx.2 r' hr' with h | h <;> omega
  present x hx := h₂.present x (h₁.present x hx)

theorem RamWriteFrame.memLoad_eq {o m : Ram} {regions : List MemoryRegion}
    (h : RamWriteFrame o m regions) {a : BitVec 64} {k : Nat} (hout : Outside regions a (k / 8)) :
    memLoad m a k = memLoad o a k := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  have := a.isLt
  have := hout.1
  have hx : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by have := hout.1; omega)]
  rw [h.outside _ ⟨by omega, fun r hr => by rcases hout.2 r hr with h' | h' <;> omega⟩]

private theorem add_ofNat_sub {a b : BitVec 64} (hba : b.toNat ≤ a.toNat) (i : Nat)
    (hi : a.toNat + i < 2 ^ 64) :
    a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (a.toNat - b.toNat + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := a.toNat - b.toNat + i) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

section Access

variable {code : CodeMap} {o m : Ram} {a b : BitVec 64} {len n : Nat}

theorem Readable.sub (h : Readable m b len) (h₁ : b.toNat ≤ a.toNat)
    (h₂ : a.toNat + n ≤ b.toNat + len) : Readable m a n := by
  have hl := h.low
  refine ⟨by omega, fun i hi => ?_⟩
  rw [add_ofNat_sub h₁ i (by omega)]
  exact h.present _ (by omega)

theorem Readable.memStore (h : Readable m a len) (b : BitVec 64) {w : Nat} (v : BitVec w) :
    Readable (memStore m b v) a len :=
  ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi)⟩

theorem Readable.of_frame (h : Readable o a len) {regions : List MemoryRegion}
    (hf : RamWriteFrame o m regions) : Readable m a len :=
  ⟨h.low, fun i hi => hf.present _ (h.present i hi)⟩

theorem Writable.sub (h : Writable code m b len) (h₁ : b.toNat ≤ a.toNat)
    (h₂ : a.toNat + n ≤ b.toNat + len) : Writable code m a n := by
  have hl := h.readable.low
  refine ⟨h.readable.sub h₁ h₂, h.tables.sub h₁ h₂, fun x hx i hi => ?_⟩
  rw [add_ofNat_sub h₁ i (by omega)]
  exact h.notCode x hx _ (by omega)

theorem Writable.memStore (h : Writable code m a len) (b : BitVec 64) {w : Nat} (v : BitVec w) :
    Writable code (memStore m b v) a len :=
  ⟨h.readable.memStore b v, h.tables, h.notCode⟩

theorem Writable.of_frame (h : Writable code o a len) {regions : List MemoryRegion}
    (hf : RamWriteFrame o m regions) : Writable code m a len :=
  ⟨h.readable.of_frame hf, h.tables, h.notCode⟩

theorem LoadOk.of_region (h : Readable m b len) (h₁ : b.toNat ≤ a.toNat)
    (h₂ : a.toNat + n ≤ b.toNat + len) : LoadOk m a n :=
  let h' := h.sub h₁ h₂
  ⟨h'.low, h'.present⟩

theorem StoreOk.of_region {p : BitVec 64} {codeLen : Nat} (h : Writable code m b len)
    (h₁ : b.toNat ≤ a.toNat) (h₂ : a.toNat + n ≤ b.toNat + len)
    (hap : RangeApart a n p codeLen) : StoreOk code m a n p codeLen :=
  let h' := h.sub h₁ h₂
  ⟨h'.readable.low, h'.readable.present, h'.tables, hap, h'.notCode⟩

section Offsets

variable {x c d : BitVec 64}

private theorem bounds_of_offsets (hlow : b.toNat + len ≤ 2 ^ 32) (ha : a = x + c)
    (hb : b = x + d) (h : (c - d).toNat + n ≤ len) :
    b.toNat ≤ a.toNat ∧ a.toNat + n ≤ b.toNat + len := by
  rw [toNat_of_offsets ha hb hlow h]
  omega

theorem Readable.of_offsets (h : Readable m b len) (ha : a = x + c) (hb : b = x + d)
    (hin : (c - d).toNat + n ≤ len) : Readable m a n :=
  have hb' := bounds_of_offsets h.low ha hb hin
  h.sub hb'.1 hb'.2

theorem Writable.of_offsets (h : Writable code m b len) (ha : a = x + c) (hb : b = x + d)
    (hin : (c - d).toNat + n ≤ len) : Writable code m a n :=
  have hb' := bounds_of_offsets h.readable.low ha hb hin
  h.sub hb'.1 hb'.2

theorem LoadOk.of_offsets (h : Readable m b len) (ha : a = x + c) (hb : b = x + d)
    (hin : (c - d).toNat + n ≤ len) : LoadOk m a n :=
  have hb' := bounds_of_offsets h.low ha hb hin
  LoadOk.of_region h hb'.1 hb'.2

theorem StoreOk.of_offsets {p : BitVec 64} {codeLen : Nat} (h : Writable code m b len)
    (ha : a = x + c) (hb : b = x + d) (hin : (c - d).toNat + n ≤ len)
    (hap : RangeApart a n p codeLen) : StoreOk code m a n p codeLen :=
  have hb' := bounds_of_offsets h.readable.low ha hb hin
  StoreOk.of_region h hb'.1 hb'.2 hap

end Offsets

end Access

namespace WordsAt

variable {m o : Ram} {base : BitVec 64} {w n : Nat} {vals : Vector (BitVec w) n}

theorem from_succ {k : Nat} (hk : k < n) (h : memLoad m (wordAddr base w k) w = vals[k])
    (hs : ∀ i (hi : i < n), k + 1 ≤ i → memLoad m (wordAddr base w i) w = vals[i]) :
    ∀ i (hi : i < n), k ≤ i → memLoad m (wordAddr base w i) w = vals[i] := by
  intro i hi hki
  rcases Nat.eq_or_lt_of_le hki with rfl | hlt
  · exact h
  · exact hs i hi hlt

theorem from_end : ∀ i (hi : i < n), n ≤ i → memLoad m (wordAddr base w i) w = vals[i] :=
  fun _ hi h => absurd hi (Nat.not_lt.mpr h)

theorem of_from (h : ∀ i (hi : i < n), 0 ≤ i → memLoad m (wordAddr base w i) w = vals[i]) :
    WordsAt m base w vals := fun i hi => h i hi (Nat.zero_le i)

private theorem mul_add_le {k i n : Nat} (hi : i < n) : k * i + k ≤ k * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

private theorem toNat_wordAddr {i : Nat} (hi : i < n) (hw0 : 0 < w / 8)
    (hn : base.toNat + w / 8 * n ≤ 2 ^ 64) :
    (wordAddr base w i).toNat = base.toNat + w / 8 * i := by
  have hmi : w / 8 * i + w / 8 ≤ w / 8 * n := mul_add_le hi
  simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := w / 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem write_set (h : WordsAt m base w vals) {j : Nat} (hj : j < n) (x : BitVec w)
    (hw : w % 8 = 0) (hw0 : 0 < w / 8) (hw128 : w ≤ 128)
    (hn : base.toNat + w / 8 * n ≤ 2 ^ 64) :
    WordsAt (memStore m (wordAddr base w j) x) base w (vals.set j x hj) := by
  intro i hi
  rw [Vector.getElem_set]
  by_cases hij : j = i
  · subst hij
    simp only [↓reduceIte]
    exact memLoad_memStore_same m _ x hw hw128
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hij), memLoad_memStore_of_rangeApart]
    · exact h i hi
    · apply RangeApart.of_toNat
      · rw [toNat_wordAddr hj hw0 hn]; have := mul_add_le (k := w / 8) hj; omega
      · rw [toNat_wordAddr hi hw0 hn]; have := mul_add_le (k := w / 8) hi; omega
      · rw [toNat_wordAddr hj hw0 hn, toNat_wordAddr hi hw0 hn]
        have := mul_add_le (k := w / 8) hj
        have := mul_add_le (k := w / 8) hi
        rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
        · have := Nat.mul_le_mul_left (w / 8) (Nat.succ_le_of_lt hlt)
          rw [Nat.mul_succ] at this; omega
        · have := Nat.mul_le_mul_left (w / 8) (Nat.succ_le_of_lt hlt)
          rw [Nat.mul_succ] at this; omega

theorem write_set' {a : BitVec 64} {x y : BitVec w} (h : WordsAt m base w vals) {j : Nat}
    (hj : j < n) (ha : a = wordAddr base w j) (hx : x = y) (hw : w % 8 = 0) (hw0 : 0 < w / 8)
    (hw128 : w ≤ 128) (hn : base.toNat + w / 8 * n ≤ 2 ^ 64) :
    WordsAt (memStore m a x) base w (vals.set j y hj) := by
  subst ha hx
  exact h.write_set hj _ hw hw0 hw128 hn

theorem write_apart (h : WordsAt m base w vals) (a : BitVec 64) {k : Nat} (x : BitVec k)
    (hap : RangeApart a (k / 8) base (w / 8 * n)) : WordsAt (memStore m a x) base w vals := by
  intro i hi
  rw [memLoad_memStore_of_rangeApart m a (wordAddr base w i) x w
    (RangeApart.right_sub hap (mul_add_le hi))]
  exact h i hi

theorem of_frame (h : WordsAt o base w vals) {regions : List MemoryRegion}
    (hf : RamWriteFrame o m regions) (hw0 : 0 < w / 8) (hout : Outside regions base (w / 8 * n)) :
    WordsAt m base w vals := by
  intro i hi
  have hmi := mul_add_le (k := w / 8) hi
  rw [hf.memLoad_eq ⟨?_, fun r hr => ?_⟩]
  · exact h i hi
  · have := hout.1
    rw [toNat_wordAddr hi hw0 (by omega)]; omega
  · have := hout.1
    rw [toNat_wordAddr hi hw0 (by omega)]
    rcases hout.2 r hr with h' | h' <;> omega

end WordsAt

end X86Proofs.Refine
