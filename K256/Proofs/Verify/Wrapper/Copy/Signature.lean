import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import Standards.NIST.SHA2.Preprocessing
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.LIR

def signatureMemory (m : Ram) (sp : BitVec 64) : Ram :=
  let n := memStore m (sp + 408) (memLoad m (sp + 72) 64)
  let n := memStore n (sp + 400) (memLoad m (sp + 64) 64)
  let n := memStore n (sp + 392) (memLoad m (sp + 56) 64)
  let n := memStore n (sp + 384) (memLoad m (sp + 48) 64)
  let n := memStore n (sp + 376) (memLoad m (sp + 40) 64)
  let n := memStore n (sp + 368) (memLoad m (sp + 32) 64)
  let n := memStore n (sp + 360) (memLoad m (sp + 24) 64)
  let n := memStore n (sp + 352) (memLoad m (sp + 16) 64)
  let n := memStore n (sp + 336) (0x5be0cd191f83d9ab : BitVec 64)
  let n := memStore n (sp + 328) (0x9b05688c510e527f : BitVec 64)
  let n := memStore n (sp + 320) (0xa54ff53a3c6ef372 : BitVec 64)
  let n := memStore n (sp + 312) (0xbb67ae856a09e667 : BitVec 64)
  let n := memStore n (sp + 344) (0 : BitVec 64)
  memStore n (sp + 311) (0 : BitVec 8)

theorem signatureMemory_frame (m : Ram) (sp : BitVec 64) (low : sp.toNat + 416 ≤ 2^32) :
    RamWriteFrame m (signatureMemory m sp) [⟨(sp + 311).toNat, 105⟩] := by
  have slot (off width : Nat) (lo : 311 ≤ off) (hi : off + width ≤ 416) :
      InRegion ⟨(sp + 311).toNat, 105⟩ (sp + BitVec.ofNat 64 off) width := by
    change (sp + 311).toNat ≤ _ ∧ _ ≤ (sp + 311).toNat + 105 ∧ _ ≤ 2^64
    have offset (k : Nat) (hk : k ≤ 416) :
        (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [offset off (by omega), show (sp + 311).toNat = sp.toNat + 311 from offset 311 (by decide)]
    omega
  unfold signatureMemory
  iterate 14
    apply RamWriteFrame.memStore
    case hin =>
      exact ⟨_, List.mem_singleton_self _, slot _ _ (by decide) (by decide)⟩
  exact .refl _ _

theorem signatureMemory_limb (m : Ram) (sp : BitVec 64) (i : Fin 8) :
    memLoad (signatureMemory m sp) (sp + BitVec.ofNat 64 (352 + 8 * i.val)) 64 =
      memLoad m (sp + BitVec.ofNat 64 (16 + 8 * i.val)) 64 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
      i.val = 6 ∨ i.val = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;>
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [signatureMemory, Nat.reduceMul, Nat.reduceAdd, memLoad_memStore_of_rangeApart] <;>
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem signatureMemory_hash (m : Ram) (sp : BitVec 64) :
    let n := signatureMemory m sp
    memLoad n (sp + 312) 64 = 0xbb67ae856a09e667 ∧
    memLoad n (sp + 320) 64 = 0xa54ff53a3c6ef372 ∧
    memLoad n (sp + 328) 64 = 0x9b05688c510e527f ∧
    memLoad n (sp + 336) 64 = 0x5be0cd191f83d9ab ∧
    memLoad n (sp + 344) 64 = 0 ∧ memLoad n (sp + 311) 8 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [signatureMemory, memLoad_memStore_same, memLoad_memStore_of_rangeApart]

theorem signatureMemory_scalars {m : Ram} {sp : BitVec 64} {r s : Vector (BitVec 64) 4}
    (hr : WordsAt m (sp + 16) 64 r) (hs : WordsAt m (sp + 48) 64 s) :
    WordsAt (signatureMemory m sp) (sp + 352) 64 r ∧
    WordsAt (signatureMemory m sp) (sp + 384) 64 s := by
  have addr (off i : Nat) :
      wordAddr (sp + BitVec.ofNat 64 off) 64 i = sp + BitVec.ofNat 64 (off + 8 * i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]
  constructor <;> intro i hi
  · rw [show wordAddr (sp + 352) 64 i = _ from addr 352 i]
    exact (signatureMemory_limb m sp ⟨i, by omega⟩).trans
      ((congrArg (fun p => memLoad m p 64) (addr 16 i).symm).trans (hr i hi))
  · have h := signatureMemory_limb m sp ⟨4 + i, by omega⟩
    change memLoad _ (sp + BitVec.ofNat 64 (352 + 8 * (4 + i))) 64 =
      memLoad m (sp + BitVec.ofNat 64 (16 + 8 * (4 + i))) 64 at h
    rw [show 16 + 8 * (4+i) = 48 + 8*i by omega,
      show 352 + 8 * (4+i) = 384 + 8*i by omega] at h
    rw [show wordAddr (sp + 384) 64 i = _ from addr 384 i]
    exact h.trans ((congrArg (fun p => memLoad m p 64) (addr 48 i).symm).trans (hs i hi))

theorem signatureMemory_initialHash (m : Ram) (sp : BitVec 64) :
    WordsAt (signatureMemory m sp) (sp + 312) 32 Standards.NIST.SHA2.SHA256.«H⁽⁰⁾» := by
  obtain ⟨w0, w1, w2, w3, _, _⟩ := signatureMemory_hash m sp
  have half {off : Nat} {v : BitVec 64} (k : Nat) (hk : k ≤ 1)
      (w : memLoad (signatureMemory m sp) (sp + BitVec.ofNat 64 off) 64 = v) :
      memLoad (signatureMemory m sp) (sp + BitVec.ofNat 64 (off + 4*k)) 32 =
        v.extractLsb' (32*k) 32 := by
    have h := extractLsb'_memLoad (signatureMemory m sp) (sp + BitVec.ofNat 64 off)
      (n := 64) (32*k) 32 (by omega) (by decide) (by omega)
    rw [w, show 32*k/8 = 4*k by omega, BitVec.add_assoc, ← BitVec.ofNat_add] at h
    exact h.symm
  intro i hi
  have addr : wordAddr (sp + 312) 32 i = sp + BitVec.ofNat 64 (312 + 4*i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [addr]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact half (off := 312) 0 (by decide) w0
  · exact half (off := 312) 1 (by decide) w0
  · exact half (off := 320) 0 (by decide) w1
  · exact half (off := 320) 1 (by decide) w1
  · exact half (off := 328) 0 (by decide) w2
  · exact half (off := 328) 1 (by decide) w2
  · exact half (off := 336) 0 (by decide) w3
  · exact half (off := 336) 1 (by decide) w3

def signatureArguments (a : Vector Value Reg.count) (m : Ram) (sp len : BitVec 64) :
    Vector Value Reg.count :=
  (((a.set 0 ⟨64, 0xbb67ae856a09e667⟩).set 1 ⟨64, memLoad m (sp + 24) 64⟩).set 16
    (.ofBool (decide (len.toNat < 63)))).set 19 (.ofBool (len == 63))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem signatureCopyBlock {a : Vector Value Reg.count} {m : Ram} {sp len : BitVec 64}
    (rsp : a[4].get 64 = sp) (length : a[3].get 64 = len)
    (win : Writable Extracted.programImage m sp 416) :
    program.runBlock (dialect Extracted.programImage) ⟨.l103037, a, m⟩ =
      .jump ⟨if 63 < len.toNat then .l10311e else .l103101,
        signatureArguments a m sp len, signatureMemory m sp⟩ := by
  have above : (¬len.toNat < 63 ∧ ¬len = 63) ↔ 63 < len.toNat := by
    have eq : len = 63 ↔ len.toNat = 63 := BitVec.toNat_inj.symm
    rw [eq]
    omega
  have branch (b : Vector Value Reg.count) (n : Ram) :
      (if 63 < len.toNat then Transfer.jump (signature := signature) (results := Reg.count)
        ⟨Label.l10311e, b, n⟩ else .jump ⟨.l103101, b, n⟩) =
      .jump ⟨if 63 < len.toNat then .l10311e else .l103101, b, n⟩ := by
    by_cases h : 63 < len.toNat <;> simp [h]
  cfg_eval [rsp, length]
  segment_words []
  iterate 22
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l103037
  simp only [above, branch]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [signatureArguments, Vector.getElem_set] <;> rfl

end K256.Proofs.Verify.Wrapper
