import Prelude.Memory
import AesGcm.Proofs.Copied.X86Proofs.Refine.Store
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Step.Paging

namespace X86Proofs

open X86 X86.Machine X86.UserProcess Prelude

variable {mem : Ram}

theorem ofNat_toNat_add (a : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (a.toNat + i) = a + BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Bytes.of_hasBytes {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes mem bytes) :
    Bytes mem (BitVec.ofNat 64 region.start) bytes.size
      (fun i => if hi : i < bytes.size then bytes[i] else 0) := by
  intro i hi
  rw [← BitVec.ofNat_add, h.2 ⟨i, hi⟩]
  simp only [hi, ↓reduceDIte]

theorem Bytes.getElem?_ofNat {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes mem a len f) {i : Nat} (hi : i < len) :
    mem[BitVec.ofNat 64 (a.toNat + i)]? = some (f i) := by
  rw [ofNat_toNat_add]
  exact h i hi

theorem Bytes.hasBytes {a : BitVec 64} {bytes : ByteArray} {f : Nat → UInt8}
    (h : Bytes mem a bytes.size f) (hf : ∀ i (hi : i < bytes.size), f i = bytes[i]) :
    (⟨a.toNat, bytes.size⟩ : MemoryRegion).HasBytes mem bytes :=
  ⟨rfl, fun i => by rw [h.getElem?_ofNat i.isLt, hf i i.isLt]⟩

end X86Proofs

namespace X86Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

variable {mem : Ram}

theorem contains_iff {r : MemoryRegion} {x : Nat} :
    r.Contains x ↔ r.start ≤ x ∧ x < r.start + r.size := by
  unfold MemoryRegion.Contains
  exact Iff.rfl

private theorem contains_add_ofNat' {region : MemoryRegion} {a : BitVec 64} {len i : Nat}
    (hstart : region.start ≤ a.toNat) (hend : a.toNat + len ≤ region.start + region.size)
    (hlow : a.toNat + len ≤ 2 ^ 64) (hi : i < len) :
    region.Contains (a + BitVec.ofNat 64 i).toNat := by
  have ha : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [MemoryRegion.Contains, ha]
  omega

theorem Readable.of_allocated {region : MemoryRegion} {a : BitVec 64} {len : Nat}
    (hbound : region.Bounded) (halloc : region.Allocated mem)
    (hstart : region.start ≤ a.toNat) (hend : a.toNat + len ≤ region.start + region.size) :
    Readable mem a len := by
  have hlow : a.toNat + len ≤ 2 ^ 32 := by
    have : region.start + region.size < 2 ^ 32 := hbound
    omega
  refine ⟨hlow, fun i hi => ?_⟩
  obtain ⟨byte, hbyte⟩ := halloc _ (contains_add_ofNat' hstart hend (by omega) hi)
  rw [hbyte]
  rfl

theorem not_pageTableEntriesApart_frames {n : Nat} (h : ¬ PageTableEntriesApart n 1) :
    0x1000 ≤ n ∧ n < 0x3000 := by
  simp only [PageTableEntriesApart] at h
  omega

theorem Writable.of_avoids {code : CodeMap} {region : MemoryRegion}
    {forbidden : BitVec 64 → Prop} {a : BitVec 64} {len : Nat}
    (hbound : region.Bounded) (halloc : region.Allocated mem)
    (havoid : region.Avoids forbidden) (hcode : ∀ x ∈ code, forbidden x.1)
    (htables : ∀ b : BitVec 64, ¬ PageTableEntriesApart b.toNat 1 → forbidden b)
    (hstart : region.start ≤ a.toNat) (hend : a.toNat + len ≤ region.start + region.size)
    (hpos : 0 < len) : Writable code mem a len := by
  have hr := Readable.of_allocated hbound halloc hstart hend
  have hc : ∀ i < len, region.Contains (a + BitVec.ofNat 64 i).toNat := fun i hi =>
    contains_add_ofNat' hstart hend (by have := hr.low; omega) hi
  refine ⟨hr, PageTableEntriesApart.of_bytes hpos hr.low fun i hi => ?_, fun x hx i hi he => ?_⟩
  · exact Decidable.byContradiction fun hn => havoid _ (hc i hi) (htables _ hn)
  · exact havoid _ (hc i hi) (he ▸ hcode x hx)

private theorem loadBytes_loop_isSome {a : BitVec 64} {count current shift accumulator : Nat}
    {value : BitVec 64} (h : loadBytes.loop mem a count current shift accumulator = .ok value)
    {i : Nat} (hi : i < count) : (mem[a + BitVec.ofNat 64 (current + i)]?).isSome := by
  induction count generalizing current shift accumulator i with
  | zero => omega
  | succ count ih =>
    cases hread : mem[addAddress a current]? with
    | none =>
      simp only [loadBytes.loop, hread] at h
      cases h
    | some byte =>
      have htail : loadBytes.loop mem a count (current + 1) (shift + 8)
          (accumulator + byte.toNat * 2 ^ shift) = .ok value := by
        simpa only [loadBytes.loop, hread] using h
      cases i with
      | zero =>
        change (mem[addAddress a current]?).isSome
        rw [hread]
        rfl
      | succ i =>
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ih htail (by omega : i < count)

theorem bytes_of_word64At {region : MemoryRegion} {value : BitVec 64}
    (h : region.Word64At mem value) :
    Bytes mem (BitVec.ofNat 64 region.start) 8 (storedByte value) := by
  have hp : ∀ i < 64 / 8, (mem[BitVec.ofNat 64 region.start + BitVec.ofNat 64 i]?).isSome :=
    fun i hi => by simpa only [Nat.zero_add] using loadBytes_loop_isSome h.2 hi
  have hb := Bytes.of_memLoad (n := 64) hp
  have hload : memLoad mem (BitVec.ofNat 64 region.start) 64 = value :=
    Except.ok.inj ((Bytes.loadBytes64 hb).symm.trans h.2)
  rwa [hload] at hb

theorem memLoad_of_word64At {region : MemoryRegion} {value : BitVec 64}
    (h : region.Word64At mem value) :
    memLoad mem (BitVec.ofNat 64 region.start) 64 = value :=
  (bytes_of_word64At h).memLoad (n := 64) (by decide) (by decide)

theorem readable_of_word64At {region : MemoryRegion} {value : BitVec 64}
    (h : region.Word64At mem value) (hbound : region.Bounded) :
    Readable mem (BitVec.ofNat 64 region.start) 8 := by
  have hlow : region.start + 8 < 2 ^ 32 := by
    have h8 : region.size = 8 := h.1.symm
    have : region.start + region.size < 2 ^ 32 := hbound
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [bytes_of_word64At h i hi]
    rfl

theorem WordsAt.of_word64At {start n : Nat} {vals : Vector (BitVec 64) n}
    (h : ∀ i (hi : i < n), (⟨start + 8 * i, 8⟩ : MemoryRegion).Word64At mem vals[i]) :
    WordsAt mem (BitVec.ofNat 64 start) 64 vals := by
  intro i hi
  have := memLoad_of_word64At (h i hi)
  rwa [BitVec.ofNat_add] at this

theorem Readable.of_word64At {start n : Nat} {vals : Nat → BitVec 64}
    (h : ∀ i < n, (⟨start + 8 * i, 8⟩ : MemoryRegion).Word64At mem (vals i))
    (hlow : start + 8 * n ≤ 2 ^ 32) :
    Readable mem (BitVec.ofNat 64 start) (8 * n) := by
  have hstart : (BitVec.ofNat 64 start).toNat = start := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [hstart]; omega, fun j hj => ?_⟩
  have hb : mem[BitVec.ofNat 64 (start + 8 * (j / 8)) + BitVec.ofNat 64 (j % 8)]? = _ :=
    bytes_of_word64At (h (j / 8) (by omega)) (j % 8) (by omega)
  rw [← BitVec.ofNat_add, Nat.add_assoc, Nat.div_add_mod] at hb
  rw [← BitVec.ofNat_add, hb]
  rfl

theorem WordsAt.of_hasBytes {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes mem bytes) :
    WordsAt mem (BitVec.ofNat 64 region.start) 8
      (Vector.ofFn fun i : Fin bytes.size => bytes[i.val].toBitVec) := by
  intro i hi
  rw [Vector.getElem_ofFn, wordAddr, show 8 / 8 * i = i by omega,
    (Bytes.of_hasBytes h).loadByte i hi]
  simp only [hi, ↓reduceDIte]

theorem Readable.of_hasBytes {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes mem bytes) (hbound : region.Bounded) :
    Readable mem (BitVec.ofNat 64 region.start) bytes.size := by
  have hlow : region.start + bytes.size < 2 ^ 32 := by
    have hs : bytes.size = region.size := h.1
    have : region.start + region.size < 2 ^ 32 := hbound
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Bytes.of_hasBytes h i hi]
    rfl

theorem apart_of_disjoint {left right : MemoryRegion} (h : left.Disjoint right)
    (hl : 0 < left.size) (hr : 0 < right.size) :
    left.start + left.size ≤ right.start ∨ right.start + right.size ≤ left.start := by
  refine Decidable.byContradiction fun hn => h (max left.start right.start) ?_ ?_ <;>
    simp only [MemoryRegion.Contains] <;> omega

theorem apart_of_avoids {region : MemoryRegion} {forbidden : BitVec 64 → Prop} {lo hi : Nat}
    (havoid : region.Avoids forbidden)
    (hforbidden : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → forbidden a)
    (hpos : 0 < region.size) (hlo : lo < hi) (hhi : hi ≤ 2 ^ 64) :
    region.start + region.size ≤ lo ∨ hi ≤ region.start := by
  refine Decidable.byContradiction fun hn => ?_
  have hmax : (BitVec.ofNat 64 (max region.start lo)).toNat = max region.start lo := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact havoid (BitVec.ofNat 64 (max region.start lo))
    (by rw [MemoryRegion.Contains, hmax]; omega)
    (hforbidden _ (by rw [hmax]; omega) (by rw [hmax]; omega))

theorem WordsAt.bytes {a : BitVec 64} {w n : Nat} {vals : Vector (BitVec w) n}
    (h : WordsAt mem a w vals) (hr : Readable mem a (w / 8 * n)) :
    Bytes mem a (w / 8 * n) (fun j =>
      if hj : j / (w / 8) < n then storedByte vals[j / (w / 8)] (j % (w / 8)) else 0) := by
  intro j hj
  have hk : 0 < w / 8 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
  have hi : j / (w / 8) < n := (Nat.div_lt_iff_lt_mul hk).2 (by rwa [Nat.mul_comm])
  have hj' : w / 8 * (j / (w / 8)) + j % (w / 8) = j := Nat.div_add_mod j (w / 8)
  simp only [hi, ↓reduceDIte]
  rw [← h _ hi, storedByte_memLoad _ _ _ (Nat.mod_lt _ hk), wordAddr,
    BitVec.add_assoc, ← BitVec.ofNat_add, hj']
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hr.present j hj)
  rw [hb]
  change some b = some ((mem[a + BitVec.ofNat 64 j]?).getD 0)
  rw [hb]
  rfl

theorem WordsAt.hasBytes {a : BitVec 64} {w n : Nat} {vals : Vector (BitVec w) n}
    {bytes : ByteArray} (h : WordsAt mem a w vals) (hr : Readable mem a (w / 8 * n))
    (hsize : bytes.size = w / 8 * n)
    (hbytes : ∀ j (hj : j < bytes.size) (hw : j / (w / 8) < n),
      bytes[j] = storedByte vals[j / (w / 8)] (j % (w / 8))) :
    (⟨a.toNat, bytes.size⟩ : MemoryRegion).HasBytes mem bytes := by
  refine Bytes.hasBytes (hsize ▸ h.bytes hr) fun j hj => ?_
  have hk : 0 < w / 8 := by
    rcases Nat.eq_zero_or_pos (w / 8) with h0 | h0
    · rw [h0, Nat.zero_mul] at hsize
      omega
    · exact h0
  have hi : j / (w / 8) < n := (Nat.div_lt_iff_lt_mul hk).2 (by rw [Nat.mul_comm]; omega)
  simp only [hi, ↓reduceDIte, hbytes j hj hi]

theorem outside_of_within {n : Nat} {regions : Vector MemoryRegion n} {small : List MemoryRegion}
    (h : ∀ r ∈ small, ∃ r' ∈ regions, ∀ x, r.Contains x → r'.Contains x) :
    ∀ x, (∀ r ∈ regions, ¬ r.Contains x) → ∀ r ∈ small, ¬ r.Contains x := by
  intro x hx r hr hc
  obtain ⟨r', hr', hsub⟩ := h r hr
  exact hx r' hr' (hsub x hc)

end X86Proofs.Refine
