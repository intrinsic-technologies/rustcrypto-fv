import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Sec1.Wrapper.Copy

open K256.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def alignmentBytes (dst : BitVec 64) : BitVec 64 :=
  ((-(dst.setWidth 32)) &&& 7).setWidth 64

def prefixBytes (dst count : BitVec 64) : BitVec 64 :=
  if count.toNat < (alignmentBytes dst).toNat then count else alignmentBytes dst

theorem alignmentBytes_toNat (dst : BitVec 64) :
    (alignmentBytes dst).toNat = (8 - dst.toNat % 8) % 8 := by
  unfold alignmentBytes
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change ((-(dst.setWidth 32)).toNat &&& (2^3 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_neg, BitVec.toNat_setWidth]
  have := dst.isLt
  omega

theorem prefixBytes_toNat (dst count : BitVec 64) :
    (prefixBytes dst count).toNat = min ((8 - dst.toNat % 8) % 8) count.toNat := by
  unfold prefixBytes
  rw [alignmentBytes_toNat]
  split
  · omega
  · rw [alignmentBytes_toNat]
    omega

theorem prefixBytes_le (dst count : BitVec 64) :
    (prefixBytes dst count).toNat ≤ count.toNat := by
  rw [prefixBytes_toNat]
  omega

theorem middleBytes_toNat (dst count : BitVec 64) :
    ((count - prefixBytes dst count) >>> 3).toNat =
      (count.toNat - (prefixBytes dst count).toNat) / 8 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  have := prefixBytes_le dst count
  have := count.isLt
  omega

theorem tailBytes_toNat (dst count : BitVec 64) :
    (((count - prefixBytes dst count).setWidth 32 &&& 7).setWidth 64).toNat =
      (count.toNat - (prefixBytes dst count).toNat) % 8 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change ((count - prefixBytes dst count).setWidth 32).toNat &&& (2^3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have := prefixBytes_le dst count
  have := count.isLt
  omega


theorem memCopy_getElem?_self (m : Ram) (dst src : BitVec 64) (len : Nat)
    (hlen : len ≤ 2 ^ 64) (i : Nat) (hi : i < len) :
    (memCopy m dst src len)[dst + BitVec.ofNat 64 i]? =
      some (memByte m (src + BitVec.ofNat 64 i)) := by
  unfold memCopy
  rw [memStore_getElem?_self_of_le m dst _ (by omega) i (by omega),
    storedByte_memLoad m src i (by omega)]

theorem memCopy_hasBytes {mem : Ram} {dst src : BitVec 64} {n : Nat} {bytes : ByteArray}
    (hlen : n ≤ 2 ^ 64) (hb : (⟨src.toNat, n⟩ : Prelude.MemoryRegion).HasBytes mem bytes) :
    (⟨dst.toNat, n⟩ : Prelude.MemoryRegion).HasBytes (memCopy mem dst src n) bytes := by
  refine ⟨hb.1, fun i => ?_⟩
  have hs : bytes.size = n := hb.1
  have hx := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx ⊢
  rw [memCopy_getElem?_self _ _ _ _ hlen _ (hs ▸ i.isLt)]
  simp only [memByte, PhysicalMemory.read, hx, Option.getD_some]

theorem memCopy_frame {initial mem : Ram} {regions : List Prelude.MemoryRegion}
    {dst src : BitVec 64} {n : Nat} (frame : RamWriteFrame initial mem regions)
    (within : InRegions regions dst n) :
    RamWriteFrame initial (memCopy mem dst src n) regions :=
  frame.memStore _ (by simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 8)] using within)

theorem memCopy_getElem?_of_ne (m : Ram) (dst src x : BitVec 64) (len : Nat)
    (hx : ∀ i < len, dst + BitVec.ofNat 64 i ≠ x) :
    (memCopy m dst src len)[x]? = m[x]? := by
  exact memStore_getElem?_of_ne m dst _ x (by
    intro i hi
    exact hx i (by omega))

theorem memCopy_append (m : Ram) (dst src : BitVec 64) (h q : Nat)
    (hlen : h + q ≤ 2 ^ 64) (hap : RangeApart src (h + q) dst (h + q)) :
    memCopy (memCopy m dst src h) (dst + BitVec.ofNat 64 h)
      (src + BitVec.ofNat 64 h) q = memCopy m dst src (h + q) := by
  have hsrc (j : Nat) (hj : j < q) :
      memByte (memCopy m dst src h) (src + BitVec.ofNat 64 (h + j)) =
        memByte m (src + BitVec.ofNat 64 (h + j)) := by
    unfold memByte
    simp only [PhysicalMemory.read]
    rw [memCopy_getElem?_of_ne]
    intro i hi he
    exact hap (h + j) (by omega) i (by omega) he.symm
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hq : ∃ j < q, dst + BitVec.ofNat 64 h + BitVec.ofNat 64 j = x
  · obtain ⟨j, hj, rfl⟩ := hq
    rw [memCopy_getElem?_self _ _ _ q (by omega) j hj]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hsrc j hj, memCopy_getElem?_self _ _ _ (h + q) hlen (h + j) (by omega)]
  · rw [memCopy_getElem?_of_ne _ _ _ x q (by
      intro j hj he
      exact hq ⟨j, hj, he⟩)]
    by_cases hh : ∃ i < h, dst + BitVec.ofNat 64 i = x
    · obtain ⟨i, hi, rfl⟩ := hh
      rw [memCopy_getElem?_self _ _ _ h (by omega) i hi,
        memCopy_getElem?_self _ _ _ (h + q) hlen i (by omega)]
    · rw [memCopy_getElem?_of_ne _ _ _ x h (by
        intro i hi he
        exact hh ⟨i, hi, he⟩)]
      symm
      apply memCopy_getElem?_of_ne
      intro i hi he
      by_cases ih : i < h
      · exact hh ⟨i, ih, he⟩
      · apply hq
        refine ⟨i - h, by omega, ?_⟩
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le (by omega : h ≤ i)] using he

theorem memCopy_three (m : Ram) (dst src : BitVec 64) (h q t : Nat)
    (hlen : h + q + t ≤ 2 ^ 64)
    (hap : RangeApart src (h + q + t) dst (h + q + t)) :
    memCopy (memCopy (memCopy m dst src h)
        (dst + BitVec.ofNat 64 h) (src + BitVec.ofNat 64 h) q)
      (dst + BitVec.ofNat 64 (h + q)) (src + BitVec.ofNat 64 (h + q)) t =
      memCopy m dst src (h + q + t) := by
  rw [memCopy_append m dst src h q (by omega) (by
    intro i hi j hj
    exact hap i (by omega) j (by omega)), memCopy_append m dst src (h + q) t hlen hap]


private theorem memcpy_returns_of_guards (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (dst src count rsp : BitVec 64)
    (hdst : args[7].get 64 = dst) (hsrc : args[6].get 64 = src)
    (hc : args[2].get 64 = count) (hsp : args[4].get 64 = rsp)
    (hdf : args[22].get 1 = 0) :
    let h := prefixBytes dst count
    let q := (count - h) >>> 3
    let t := ((count - h).setWidth 32 &&& 7).setWidth 64
    let mem₁ := memCopy mem dst src h.toNat
    let mem₂ := memCopy mem₁ (dst + BitVec.ofNat 64 h.toNat)
      (src + BitVec.ofNat 64 h.toNat) (8 * q.toNat)
    let mem₃ := memCopy mem₂ (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t.toNat
    RepMovsOk code mem 0 src dst h 1 0x12a837 2 →
    (RepMovsOk code mem₁ 0
      (src + BitVec.ofNat 64 h.toNat) (dst + BitVec.ofNat 64 h.toNat) q 8 0x12a843 3) →
    RepMovsOk code mem₂ 0
      (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t 1 0x12a84c 2 →
    (LoadOk mem₃ rsp 8 ∧ (memLoad mem₃ rsp 64).toNat < 2^32) →
    ∃ output, LIR.program.runBlock (dialect code) ⟨.l12a820, args, mem⟩ = .returned output ∧
      output.store = mem₃ ∧ output.tag = some ⟨64, memLoad output.store rsp 64⟩ ∧
      output.values[0] = ⟨64, dst⟩ ∧ output.values[4] = ⟨64, rsp + 8⟩ ∧
      output.values[3] = args[3] ∧ output.values[5] = args[5] ∧
      output.values[9] = args[9] ∧ output.values[10] = args[10] ∧ output.values[11] = args[11] ∧
      output.values[12] = args[12] ∧ output.values[13] = args[13] ∧
      output.values[14] = args[14] ∧ output.values[15] = args[15] ∧
      output.values[22] = args[22] ∧ output.values[39] = args[39] ∧
      output.values[50] = args[50] ∧ output.values[51] = args[51] := by
  dsimp only
  intro hfirst hmiddle hlast hret
  have hprefix : (if (cmpSpec count (((-(dst.setWidth 32)) &&& 7).setWidth 64)).CF = true
      then count else ((-(dst.setWidth 32)) &&& 7).setWidth 64) = prefixBytes dst count := by
    simp only [prefixBytes, alignmentBytes, cmpSpec, subSpec, decide_eq_true_eq]
    rfl
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [hdst, hsrc, hc, hsp, hdf, hprefix]
    simp (config := { bitVecOfNat := false }) only [hprefix, hfirst, hmiddle, hlast, hret,
      or_true, ↓reduceIte]
    rfl
  case post => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem repMovsOk_of_regions {code : CodeMap} {mem : Ram} {df : BitVec 1}
    {src dst count p : BitVec 64} {size : Nat} {bytes : List UInt8}
    (hr : Readable mem src (size * count.toNat))
    (hw : Writable code mem dst (size * count.toNat)) (hdf : df = 0)
    (hap : src.toNat + size * count.toNat ≤ dst.toNat ∨ dst.toNat + size * count.toNat ≤ src.toNat)
    (hcode : ∀ x ∈ codeRange p bytes, x ∈ code) :
    RepMovsOk code mem df src dst count size p bytes.length := by
  refine ⟨hdf, hr.low, hw.readable.low, hr.present, hw.readable.present, hap, hw.tables, ?_, hw.notCode⟩
  intro i hi j hj he
  exact hw.notCode _ (hcode _ (mem_codeRange p bytes j hj)) i hi he.symm

theorem memcpy {args : Values Value Reg.count} {mem : Ram} {dst src count rsp : BitVec 64}
    (hdst : args[7].get 64 = dst) (hsrc : args[6].get 64 = src)
    (hc : args[2].get 64 = count) (hsp : args[4].get 64 = rsp) (hdf : args[22].get 1 = 0)
    (hr : Readable mem src count.toNat) (hw : Writable Extracted.programImage mem dst count.toNat)
    (hdisjoint : src.toNat + count.toNat ≤ dst.toNat ∨ dst.toNat + count.toNat ≤ src.toNat)
    (hapret : RangeApart dst count.toNat rsp 8)
    (hreturnRead : Readable mem rsp 8) (hretlow : (memLoad mem rsp 64).toNat < 2 ^ 32) :
    ∃ output, program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820, args, mem⟩, []⟩ output ∧
      output.store = memCopy mem dst src count.toNat ∧
      output.tag = some ⟨64, memLoad mem rsp 64⟩ ∧
      output.values[0] = ⟨64, dst⟩ ∧ output.values[4] = ⟨64, rsp + 8⟩ ∧
      (∀ i : Fin 53, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → output.values[i] = args[i]) := by
  let h := prefixBytes dst count
  let q := (count - h) >>> 3
  let t := ((count - h).setWidth 32 &&& 7).setWidth 64
  let mem₁ := memCopy mem dst src h.toNat
  let mem₂ := memCopy mem₁ (dst + BitVec.ofNat 64 h.toNat)
    (src + BitVec.ofNat 64 h.toNat) (8 * q.toNat)
  let mem₃ := memCopy mem₂ (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
    (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t.toNat
  have hh : h.toNat < 8 ∧ h.toNat ≤ count.toNat := by
    dsimp only [h]
    rw [prefixBytes_toNat]
    omega
  have hq : q.toNat = (count.toNat - h.toNat) / 8 := middleBytes_toNat _ _
  have ht : t.toNat = (count.toNat - h.toNat) % 8 := tailBytes_toNat _ _
  have htotal : h.toNat + 8 * q.toNat + t.toNat = count.toNat := by omega
  have hdNat (off : Nat) (hoff : off ≤ count.toNat) :
      (dst + BitVec.ofNat 64 off).toNat = dst.toNat + off := by
    have := hw.readable.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hsNat (off : Nat) (hoff : off ≤ count.toNat) :
      (src + BitVec.ofNat 64 off).toNat = src.toNat + off := by
    have := hr.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hcode₁ : ∀ x ∈ codeRange 0x12a837 [0xF3, 0xA4], x ∈ Extracted.programImage := by
    intro x hx
    exact Common.fnCode_subset_programImage x <| code_l12a820 x (codeRange_mem_of_drop (p := 0x12a820)
      (all := bytes_l12a820) 23 (by decide +kernel) x hx)
  have hcode₂ : ∀ x ∈ codeRange 0x12a843 [0xF3, 0x48, 0xA5], x ∈ Extracted.programImage := by
    intro x hx
    exact Common.fnCode_subset_programImage x <| code_l12a820 x (codeRange_mem_of_drop (p := 0x12a820)
      (all := bytes_l12a820) 35 (by decide +kernel) x hx)
  have hcode₃ : ∀ x ∈ codeRange 0x12a84c [0xF3, 0xA4], x ∈ Extracted.programImage := by
    intro x hx
    exact Common.fnCode_subset_programImage x <| code_l12a820 x (codeRange_mem_of_drop (p := 0x12a820)
      (all := bytes_l12a820) 44 (by decide +kernel) x hx)
  have hfirst := repMovsOk_of_regions
    (hr.sub (Nat.le_refl _) (by omega) : Readable mem src (1 * h.toNat))
    (hw.sub (Nat.le_refl _) (by omega)) (df := 0) rfl (by omega) hcode₁
  have hr₁ : Readable mem₁ src count.toNat :=
    hr.memStore dst (memLoad mem src (8 * h.toNat))
  have hw₁ : Writable Extracted.programImage mem₁ dst count.toNat :=
    hw.memStore dst (memLoad mem src (8 * h.toNat))
  have hmDst : (dst + BitVec.ofNat 64 h.toNat).toNat = dst.toNat + h.toNat :=
    hdNat _ (by omega)
  have hmSrc : (src + BitVec.ofNat 64 h.toNat).toNat = src.toNat + h.toNat :=
    hsNat _ (by omega)
  have hmiddle : RepMovsOk Extracted.programImage mem₁ 0
      (src + BitVec.ofNat 64 h.toNat) (dst + BitVec.ofNat 64 h.toNat)
      q 8 0x12a843 3 := by
    exact repMovsOk_of_regions
      (hr₁.sub (a := src + BitVec.ofNat 64 h.toNat) (by omega) (by omega) :
        Readable mem₁ (src + BitVec.ofNat 64 h.toNat) (8 * q.toNat))
      (hw₁.sub (a := dst + BitVec.ofNat 64 h.toNat) (by omega) (by omega))
      (df := 0) rfl
      (by omega) hcode₂
  have hr₂ : Readable mem₂ src count.toNat :=
    hr₁.memStore (dst + BitVec.ofNat 64 h.toNat)
      (memLoad mem₁ (src + BitVec.ofNat 64 h.toNat) (8 * (8 * q.toNat)))
  have hw₂ : Writable Extracted.programImage mem₂ dst count.toNat :=
    hw₁.memStore (dst + BitVec.ofNat 64 h.toNat)
      (memLoad mem₁ (src + BitVec.ofNat 64 h.toNat) (8 * (8 * q.toNat)))
  have htDst : (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)).toNat =
      dst.toNat + h.toNat + 8 * q.toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hdNat _ (by omega)]
    omega
  have htSrc : (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)).toNat =
      src.toNat + h.toNat + 8 * q.toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsNat _ (by omega)]
    omega
  have hlast := repMovsOk_of_regions
    (hr₂.sub (a := src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (by omega) (by omega) : Readable mem₂
        (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) (1 * t.toNat))
    (hw₂.sub (a := dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (by omega) (by omega)) (df := 0) rfl (by omega) hcode₃
  have hap : RangeApart src count.toNat dst count.toNat :=
    RangeApart.of_toNat (by have := hr.low; omega) (by have := hw.readable.low; omega) hdisjoint
  have hcopy : mem₃ = memCopy mem dst src count.toNat := by
    dsimp only [mem₃, mem₂, mem₁]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [memCopy_three _ _ _ _ _ _ (by have := hr.low; omega) (by simpa only [htotal] using hap), htotal]
  have hreturn : memLoad mem₃ rsp 64 = memLoad mem rsp 64 := by
    rw [hcopy]
    unfold memCopy
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (by
      simpa only [show 8 * count.toNat / 8 = count.toNat by omega] using hapret)]
  have hread : Readable mem₃ rsp 8 := by
    rw [hcopy]
    exact hreturnRead.memStore dst (memLoad mem src (8 * count.toNat))
  obtain ⟨output, step, store, tag, r0, r4, r3, r5, r9, r10, r11, r12, r13, r14, r15, df, mxcsr, ftw, fcw⟩ :=
    memcpy_returns_of_guards Extracted.programImage args mem dst src count rsp hdst hsrc hc hsp hdf
      hfirst hmiddle hlast ⟨⟨hread.low, hread.present⟩, by rw [hreturn]; exact hretlow⟩
  refine ⟨output, .done (congrArg (Transfer.next _ []) step), store.trans hcopy, ?_, r0, r4, ?_⟩
  · rw [tag, store, hreturn]
  · rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> assumption

end K256.Proofs.Sec1.Wrapper.Copy
