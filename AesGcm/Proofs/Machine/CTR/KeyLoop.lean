import AesGcm.Proofs.Machine.CTR.KeyWidening
import AesGcm.Proofs.Machine.CTR.KeyMemory
import AesGcm.Proofs.Machine.Runtime.Guards

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def keyWords (use256 : Bool) : Nat := if use256 then 120 else 88

def wideningOffset (use256 : Bool) : BitVec 64 := if use256 then 0x518 else 0x418

def wideningLabel (use256 : Bool) : LIR.Label := if use256 then .l108520 else .l107090

def wideningExit (use256 : Bool) : LIR.Label := if use256 then .l10856d else .l1070dd

theorem widening_address (use256 : Bool) (sp : BitVec 64) (k : Nat) :
    sp + (BitVec.ofNat 64 k <<< 3) + wideningOffset use256 =
      sp + wideningOffset use256 + BitVec.ofNat 64 (8 * k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change sp + (BitVec.ofNat 64 k * BitVec.ofNat 64 8) + wideningOffset use256 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm k 8]
  ac_rfl

theorem widening_source_address (src : BitVec 64) (k : Nat) :
    src + (BitVec.ofNat 64 k <<< 1) = src + BitVec.ofNat 64 (2 * k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change src + (BitVec.ofNat 64 k * BitVec.ofNat 64 2) = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm k 2]

theorem widening_store_guard (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (mem : Ram) (dst : BitVec 64)
    (hw : Writable code mem dst 8) :
    StoreOk code mem dst 8 (if use256 then 0x10855c else 0x1070cc) 8 := by
  cases use256
  · have ha := storeOk_of_codeRange hw (fun x hx ↦ hcode x (LIR.code_l107090 x hx))
    apply storeOk_of_writable hw
    have hb : LIR.bytes_l107090.length = 77 := by decide +kernel
    have hr := RangeApart.right_sub ha.apart (off := 60) (m' := 8) (by rw [hb]; decide)
    exact hr
  · have ha := storeOk_of_codeRange hw (fun x hx ↦ hcode x (LIR.code_l108520 x hx))
    apply storeOk_of_writable hw
    have hb : LIR.bytes_l108520.length = 77 := by decide +kernel
    have hr := RangeApart.right_sub ha.apart (off := 60) (m' := 8) (by rw [hb]; decide)
    exact hr

set_option maxHeartbeats 800000 in
theorem widening_loop (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (keys : Vector (BitVec 16) (keyWords use256)) (k : Nat) (hk : k < keyWords use256)
    (args : Values Value Reg.count) (src sp : BitVec 64) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hread : Readable mem src (2 * keyWords use256))
    (hwrite : Writable code mem (sp + wideningOffset use256) (8 * keyWords use256))
    (hapart : RangeApart (sp + wideningOffset use256) (8 * keyWords use256)
      src (2 * keyWords use256))
    (hkeys : WordsAt mem src 16 keys)
    (hprefix : ∀ i (hi : i < keyWords use256), i < k →
      memLoad mem (sp + wideningOffset use256 + BitVec.ofNat 64 (8 * i)) 64 =
        Fixslice16.widenWord keys[i]) :
    ∃ next : Location Value Ram LIR.Label signature,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨wideningLabel use256, wideningRegisters args src sp (BitVec.ofNat 64 k), mem⟩, []⟩
        ⟨next, []⟩ ∧
      next.label = wideningExit use256 ∧
      WordsAt next.store (sp + wideningOffset use256) 64 (keys.map Fixslice16.widenWord) ∧
      RamWriteFrame mem next.store [span (sp + wideningOffset use256) (8 * keyWords use256)] ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, BitVec.ofNat 64 (keyWords use256)⟩ ∧
      (∀ r : Fin 53, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 19 →
        next.arguments[r.val]'(by exact r.isLt) =
          (wideningRegisters args src sp (BitVec.ofNat 64 k))[r.val]) ∧
      GPRsTyped next.arguments := by
  have hn : keyWords use256 ≤ 120 := by cases use256 <;> decide
  induction hd : keyWords use256 - k using Nat.strongRecOn generalizing k args mem with
  | ind d ih =>
    have hsaddr (j : Nat) (hj : j < keyWords use256) :
        (src + BitVec.ofNat 64 (2 * j)).toNat = src.toNat + 2 * j := by
      have hl := hread.low
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := 2 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
    have hdaddr (j : Nat) (hj : j < keyWords use256) :
        (sp + wideningOffset use256 + BitVec.ofNat 64 (8 * j)).toNat =
          (sp + wideningOffset use256).toNat + 8 * j := by
      have hl := hwrite.readable.low
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := 8 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
    have hl : LoadOk mem (src + (BitVec.ofNat 64 k <<< 1)) 2 := by
      rw [widening_source_address]
      apply LoadOk.of_region hread <;> rw [hsaddr k hk] <;> omega
    have hw : StoreOk code mem
        (sp + (BitVec.ofNat 64 k <<< 3) + (if use256 then 0x518 else 0x418)) 8
        (if use256 then 0x10855c else 0x1070cc) 8 := by
      change StoreOk code mem (sp + (BitVec.ofNat 64 k <<< 3) + wideningOffset use256) 8 _ 8
      rw [widening_address]
      apply widening_store_guard use256 code hcode
      apply hwrite.sub <;> rw [hdaddr k hk] <;> omega
    obtain ⟨mid, hstep, hlabel, hmem, hindex, hregs, htypes⟩ :=
      widening_step use256 code args src sp (BitVec.ofNat 64 k) mem hTypes hl hw
    have hkey : memLoad mem (src + BitVec.ofNat 64 (2 * k)) 16 = keys[k] := hkeys k hk
    change mid.store = memStore mem (sp + (BitVec.ofNat 64 k <<< 3) + wideningOffset use256)
      (Fixslice16.widenWord (memLoad mem (src + (BitVec.ofNat 64 k <<< 1)) 16)) at hmem
    rw [widening_address, widening_source_address, hkey] at hmem
    have hbnd : (sp + wideningOffset use256).toNat + 8 * keyWords use256 ≤ 2^64 := by
      have := hwrite.readable.low
      omega
    obtain ⟨hkeys', hprefix', hframe⟩ := widening_store keys mem src
      (sp + wideningOffset use256) hk hbnd hapart hkeys hprefix
    rw [← hmem] at hkeys' hprefix' hframe
    have hread' : Readable mid.store src (2 * keyWords use256) :=
      hread.of_frame hframe
    have hwrite' : Writable code mid.store (sp + wideningOffset use256)
        (8 * keyWords use256) := hwrite.of_frame hframe
    have hiadd : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [hiadd] at hindex hlabel
    have hnormalized : wideningRegisters mid.arguments src sp (BitVec.ofNat 64 (k + 1)) =
        mid.arguments := by
      apply wideningRegisters_eq
      · exact hregs 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hindex
      · exact hregs 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hregs 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hregs 6 (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hregs 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    by_cases hend : k + 1 = keyWords use256
    · refine ⟨mid, Semantics.Reaches.single hstep, ?_, ?_, hframe, ?_, hregs, htypes⟩
      · cases use256 <;> simpa only [hend, keyWords, wideningExit,
          Bool.false_eq_true, BitVec.ofNat_eq_ofNat, ↓reduceIte] using hlabel
      · intro i hi
        simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_map] using hprefix' i hi (by omega)
      · simpa only [hend] using hindex
    · have hlt : k + 1 < keyWords use256 := by omega
      have hremaining : keyWords use256 - (k + 1) < d := by omega
      have hcount : (if use256 then 120 else 88 : BitVec 64) =
          BitVec.ofNat 64 (keyWords use256) := by cases use256 <;> rfl
      have hne : BitVec.ofNat 64 (k + 1) ≠ BitVec.ofNat 64 (keyWords use256) := by
        intro he
        have he' := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at he'
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he'
        omega
      have hmidlabel : mid.label = wideningLabel use256 := by
        rw [hcount, ite_eq_right hne] at hlabel
        exact hlabel
      obtain ⟨next, hreach, hfinal, hwords, hframe', hindex', hregs', htypes'⟩ :=
        ih _ hremaining (k + 1) hlt mid.arguments mid.store htypes hread' hwrite'
          hkeys' hprefix' rfl
      have hmid : (⟨wideningLabel use256,
          wideningRegisters mid.arguments src sp (BitVec.ofNat 64 (k + 1)),
          mid.store⟩ : Location Value Ram LIR.Label signature) = mid := by
        cases mid
        congr 1
        · exact hmidlabel.symm
      rw [hmid] at hreach
      refine ⟨next, (Semantics.Reaches.single hstep).trans hreach, hfinal, hwords,
        hframe.trans hframe' (fun r hr ↦ ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
        hindex', ?_, htypes'⟩
      intro r h1 h8 h9 h10 h19
      rw [hregs' r h1 h8 h9 h10 h19, hnormalized]
      exact hregs r h1 h8 h9 h10 h19

end AesGcm.Proofs.Machine.CTR
