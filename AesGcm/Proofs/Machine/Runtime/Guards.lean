import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine X86Proofs.Lift

theorem disjoint_bounds (a n b m : Nat) (hn : 0 < n) (hm : 0 < m)
    (h : (⟨a, n⟩ : MemoryRegion).Disjoint ⟨b, m⟩) : a + n ≤ b ∨ b + m ≤ a := by
  change (∀ x, a ≤ x ∧ x < a + n → ¬ (b ≤ x ∧ x < b + m)) at h
  by_cases hab : a ≤ b
  · left
    apply Nat.le_of_not_gt
    intro hgap
    exact h b ⟨hab, hgap⟩ ⟨Nat.le_refl _, by omega⟩
  · right
    apply Nat.le_of_not_gt
    intro hgap
    exact h a ⟨Nat.le_refl _, by omega⟩ ⟨by omega, hgap⟩

theorem storeOk_of_writable {code : CodeMap} {mem : Ram} {addr p : BitVec 64}
    {len codeLen : Nat} (h : Writable code mem addr len)
    (hap : RangeApart addr len p codeLen) : StoreOk code mem addr len p codeLen :=
  ⟨h.readable.low, h.readable.present, h.tables, hap, h.notCode⟩

theorem storeOk_of_codeRange {code : CodeMap} {mem : Ram} {addr p : BitVec 64}
    {len : Nat} {bytes : List UInt8} (h : Writable code mem addr len)
    (hc : ∀ x ∈ codeRange p bytes, x ∈ code) :
    StoreOk code mem addr len p bytes.length := by
  refine ⟨h.readable.low, h.readable.present, h.tables, ?_, h.notCode⟩
  intro i hi j hj he
  exact h.notCode _ (hc _ (mem_codeRange p bytes j hj)) i hi he.symm

theorem repStosOk_of_region {code : CodeMap} {mem : Ram} {df : BitVec 1}
    {dst count p : BitVec 64} {size : Nat} {bytes : List UInt8}
    (hw : Writable code mem dst (size * count.toNat)) (hdf : df = 0)
    (hcode : ∀ x ∈ codeRange p bytes, x ∈ code) :
    RepStosOk code mem df dst count size p bytes.length :=
  ⟨hdf, hw.readable.low, hw.readable.present, hw.tables,
    (storeOk_of_codeRange hw hcode).apart, hw.notCode⟩

theorem repMovsOk_of_regions {code : CodeMap} {mem : Ram} {df : BitVec 1}
    {src dst count p : BitVec 64} {size : Nat} {bytes : List UInt8}
    (hr : Readable mem src (size * count.toNat))
    (hw : Writable code mem dst (size * count.toNat)) (hdf : df = 0)
    (hdisjoint : src.toNat + size * count.toNat ≤ dst.toNat ∨
      dst.toNat + size * count.toNat ≤ src.toNat)
    (hcode : ∀ x ∈ codeRange p bytes, x ∈ code) :
    RepMovsOk code mem df src dst count size p bytes.length :=
  ⟨hdf, hr.low, hw.readable.low, hr.present, hw.readable.present, hdisjoint,
    hw.tables, (storeOk_of_codeRange hw hcode).apart, hw.notCode⟩

theorem storeOk_memStore {code : CodeMap} {mem : Ram}
    {a p : BitVec 64} {len codeLen : Nat} (h : StoreOk code mem a len p codeLen)
    (b : BitVec 64) {w : Nat} (v : BitVec w) :
    StoreOk code (memStore mem b v) a len p codeLen :=
  ⟨h.low, fun i hi ↦ memStore_isSome mem b v _ (h.present i hi),
    h.tables, h.apart, h.notCode⟩


theorem loadOk_memStore {mem : Ram} {a : BitVec 64} {len : Nat}
    (h : LoadOk mem a len) (b : BitVec 64) {w : Nat} (v : BitVec w) :
    LoadOk (memStore mem b v) a len :=
  ⟨h.low, fun i hi ↦ memStore_isSome mem b v _ (h.present i hi)⟩

theorem readable_append {mem : Ram} {a : BitVec 64} {n k : Nat}
    (h1 : Readable mem a n) (h2 : Readable mem (a + BitVec.ofNat 64 n) k) :
    Readable mem a (n + k) := by
  have hlow1 := h1.low
  have ha : (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlow2 := h2.low
  rw [ha] at hlow2
  refine ⟨by omega, ?_⟩
  intro i hi
  by_cases hin : i < n
  · exact h1.present i hin
  · have he : a + BitVec.ofNat 64 i =
        (a + BitVec.ofNat 64 n) + BitVec.ofNat 64 (i - n) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
    rw [he]
    exact h2.present (i - n) (by omega)


end AesGcm.Proofs.Machine.Runtime
