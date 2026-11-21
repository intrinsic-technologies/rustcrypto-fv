import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.LIR.Fn103f00.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Chunks
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Machine.Runtime.Partition
import AesGcm.Proofs.Copied.X86Proofs.Lift.Rep
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Proofs.Machine.Runtime Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

private theorem memcpy_returns_of_guards (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (dst src count rsp : BitVec 64)
    (hdst : args[7].get 64 = dst) (hsrc : args[6].get 64 = src)
    (hc : args[2].get 64 = count) (hsp : args[4].get 64 = rsp)
    (hdf : args[22].get 1 = 0) (htypes : GPRsTyped args) :
    let h := prefixBytes dst count
    let q := (count - h) >>> 3
    let t := ((count - h).setWidth 32 &&& 7).setWidth 64
    let mem₁ := memCopy mem dst src h.toNat
    let mem₂ := memCopy mem₁ (dst + BitVec.ofNat 64 h.toNat)
      (src + BitVec.ofNat 64 h.toNat) (8 * q.toNat)
    let mem₃ := memCopy mem₂ (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t.toNat
    RepMovsOk code mem 0 src dst h 1 0x103f17 2 →
    RepMovsOk code mem₁ 0
      (src + BitVec.ofNat 64 h.toNat) (dst + BitVec.ofNat 64 h.toNat) q 8 0x103f23 3 →
    RepMovsOk code mem₂ 0
      (src + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t 1 0x103f2c 2 →
    (LoadOk mem₃ rsp 8 ∧ (memLoad mem₃ rsp 64).toNat < 2^32) →
    ∃ output, LIR.program.runBlock (dialect code) ⟨.l103f00, args, mem⟩ = .returned output ∧
      output.store = mem₃ ∧ output.tag = some ⟨64, memLoad output.store rsp 64⟩ ∧
      output.values[0] = ⟨64, dst⟩ ∧ output.values[4] = ⟨64, rsp + 8⟩ ∧
      output.values[3] = args[3] ∧ output.values[5] = args[5] ∧
      output.values[12] = args[12] ∧ output.values[13] = args[13] ∧
      output.values[14] = args[14] ∧ output.values[15] = args[15] ∧
      output.values[22] = args[22] ∧
      output.values[39] = args[39] ∧ output.values[50] = args[50] ∧
      output.values[51] = args[51] ∧ GPRsTyped output.values := by
  dsimp only
  intro hfirst hmiddle hlast hret
  have hprefix : (if (cmpSpec count (((-(dst.setWidth 32)) &&& 7).setWidth 64)).CF = true
      then count else ((-(dst.setWidth 32)) &&& 7).setWidth 64) = prefixBytes dst count := by
    simp only [prefixBytes, alignmentBytes, cmpSpec, subSpec, decide_eq_true_eq]
    rfl
  cfg_eval [LIR.program, hdst, hsrc, hc, hsp, hdf, hprefix]
  simp (config := { bitVecOfNat := false }) only [hprefix, hfirst, hmiddle, hlast, hret,
    or_true, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply GPRsTyped.of_updates htypes [0, 1, 2, 4, 6, 7, 8]
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rintro ⟨r, hr⟩ hout
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
    have hc : r = 3 ∨ r = 5 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨
        r = 14 ∨ r = 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


def memcpyPre (code : CodeMap) (fr : Activation) (mem : Ram) : Prop :=
  Readable mem fr.rsi fr.rdx.toNat ∧
    Writable code mem fr.rdi fr.rdx.toNat ∧
    (fr.rsi.toNat + fr.rdx.toNat ≤ fr.rdi.toNat ∨
      fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsi.toNat) ∧
    RangeApart fr.rdi fr.rdx.toNat fr.rsp 8

theorem memcpy_call (code : CodeMap)
    (hcode : ∀ x ∈ codeRange 0x103f00 LIR.bytes_l103f00, x ∈ code) :
    CallContract LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
      (fun fr => [span fr.rdi fr.rdx.toNat]) (memcpyPre code)
      (fun fr mem => ∀ i < fr.rdx.toNat,
        mem[fr.rdi + BitVec.ofNat 64 i]? = fr.original[fr.rsi + BitVec.ofNat 64 i]?) := by
  intro fr loc hlabel hmem hentry htypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hlabel hmem hentry htypes hpre
  subst label
  subst mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ fr.low.toNat ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, hc, hbx, hbp, hsrc, hdst, -, -, h12, h13, h14, h15, h39, h50, h51,
    hreturnRead, hreturnValue, hretlow, -, -, -⟩
  rcases hpre with ⟨hr, hw, hdisjoint, hapret⟩
  let h := prefixBytes fr.rdi fr.rdx
  let q := (fr.rdx - h) >>> 3
  let t := ((fr.rdx - h).setWidth 32 &&& 7).setWidth 64
  let mem₁ := memCopy fr.original fr.rdi fr.rsi h.toNat
  let mem₂ := memCopy mem₁ (fr.rdi + BitVec.ofNat 64 h.toNat)
    (fr.rsi + BitVec.ofNat 64 h.toNat) (8 * q.toNat)
  let mem₃ := memCopy mem₂ (fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
    (fr.rsi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t.toNat
  have hh : h.toNat < 8 ∧ h.toNat ≤ fr.rdx.toNat := by
    dsimp only [h]
    rw [prefixBytes_toNat]
    omega
  have hq : q.toNat = (fr.rdx.toNat - h.toNat) / 8 := middleBytes_toNat _ _
  have ht : t.toNat = (fr.rdx.toNat - h.toNat) % 8 := tailBytes_toNat _ _
  have htotal : h.toNat + 8 * q.toNat + t.toNat = fr.rdx.toNat := by omega
  have hdNat (off : Nat) (hoff : off ≤ fr.rdx.toNat) :
      (fr.rdi + BitVec.ofNat 64 off).toNat = fr.rdi.toNat + off := by
    have := hw.readable.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hsNat (off : Nat) (hoff : off ≤ fr.rdx.toNat) :
      (fr.rsi + BitVec.ofNat 64 off).toNat = fr.rsi.toNat + off := by
    have := hr.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hcode₁ : ∀ x ∈ codeRange 0x103f17 [0xF3, 0xA4], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := 0x103f00)
      (all := LIR.bytes_l103f00) 23 (by decide +kernel) x hx)
  have hcode₂ : ∀ x ∈ codeRange 0x103f23 [0xF3, 0x48, 0xA5], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := 0x103f00)
      (all := LIR.bytes_l103f00) 35 (by decide +kernel) x hx)
  have hcode₃ : ∀ x ∈ codeRange 0x103f2c [0xF3, 0xA4], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := 0x103f00)
      (all := LIR.bytes_l103f00) 44 (by decide +kernel) x hx)
  have hfirst := repMovsOk_of_regions
    (hr.sub (Nat.le_refl _) (by omega) : Readable fr.original fr.rsi (1 * h.toNat))
    (hw.sub (Nat.le_refl _) (by omega)) (df := 0) rfl (by omega) hcode₁
  have hr₁ : Readable mem₁ fr.rsi fr.rdx.toNat :=
    hr.memStore fr.rdi (memLoad fr.original fr.rsi (8 * h.toNat))
  have hw₁ : Writable code mem₁ fr.rdi fr.rdx.toNat :=
    hw.memStore fr.rdi (memLoad fr.original fr.rsi (8 * h.toNat))
  have hmDst : (fr.rdi + BitVec.ofNat 64 h.toNat).toNat = fr.rdi.toNat + h.toNat :=
    hdNat _ (by omega)
  have hmSrc : (fr.rsi + BitVec.ofNat 64 h.toNat).toNat = fr.rsi.toNat + h.toNat :=
    hsNat _ (by omega)
  have hmiddle := repMovsOk_of_regions
    (hr₁.sub (a := fr.rsi + BitVec.ofNat 64 h.toNat) (by omega) (by omega) :
      Readable mem₁ (fr.rsi + BitVec.ofNat 64 h.toNat) (8 * q.toNat))
    (hw₁.sub (a := fr.rdi + BitVec.ofNat 64 h.toNat) (by omega) (by omega))
    (df := 0) rfl (by omega) hcode₂
  have hr₂ : Readable mem₂ fr.rsi fr.rdx.toNat :=
    hr₁.memStore (fr.rdi + BitVec.ofNat 64 h.toNat)
      (memLoad mem₁ (fr.rsi + BitVec.ofNat 64 h.toNat) (8 * (8 * q.toNat)))
  have hw₂ : Writable code mem₂ fr.rdi fr.rdx.toNat :=
    hw₁.memStore (fr.rdi + BitVec.ofNat 64 h.toNat)
      (memLoad mem₁ (fr.rsi + BitVec.ofNat 64 h.toNat) (8 * (8 * q.toNat)))
  have htDst : (fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)).toNat =
      fr.rdi.toNat + h.toNat + 8 * q.toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hdNat _ (by omega)]
    omega
  have htSrc : (fr.rsi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)).toNat =
      fr.rsi.toNat + h.toNat + 8 * q.toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsNat _ (by omega)]
    omega
  have hlast := repMovsOk_of_regions
    (hr₂.sub (a := fr.rsi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (by omega) (by omega) : Readable mem₂
        (fr.rsi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) (1 * t.toNat))
    (hw₂.sub (a := fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (by omega) (by omega)) (df := 0) rfl (by omega) hcode₃
  have hap : RangeApart fr.rsi fr.rdx.toNat fr.rdi fr.rdx.toNat :=
    RangeApart.of_toNat (by have := hr.low; omega) (by have := hw.readable.low; omega) hdisjoint
  have hcopy : mem₃ = memCopy fr.original fr.rdi fr.rsi fr.rdx.toNat := by
    dsimp only [mem₃, mem₂, mem₁]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [memCopy_three _ _ _ _ _ _ (by have := hr.low; omega) (by simpa only [htotal] using hap), htotal]
  have hreturn : memLoad mem₃ fr.rsp 64 = fr.ret := by
    rw [hcopy]
    unfold memCopy
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (by
      simpa only [show 8 * fr.rdx.toNat / 8 = fr.rdx.toNat by omega] using hapret), hreturnValue]
  have hread : Readable mem₃ fr.rsp 8 := by
    rw [hcopy]
    exact hreturnRead.memStore fr.rdi (memLoad fr.original fr.rsi (8 * fr.rdx.toNat))
  obtain ⟨output, hblock, hstore, htag, ho0, ho4, ho3, ho5, ho12, ho13, ho14, ho15, ho22, ho39, ho50, ho51, hotypes⟩ :=
    memcpy_returns_of_guards code args fr.original fr.rdi fr.rsi fr.rdx fr.rsp
      (by rw [hdst]; rfl) (by rw [hsrc]; rfl) (by rw [hc]; rfl)
      (by rw [hsp]; rfl) (by rw [hdf]; rfl) htypes hfirst hmiddle hlast
      ⟨⟨hread.low, hread.present⟩, by rw [hreturn]; exact hretlow⟩
  have hfinalStore : output.store = memCopy fr.original fr.rdi fr.rsi fr.rdx.toNat :=
    (show output.store = mem₃ from hstore).trans hcopy
  refine ⟨output, .done ?_, ?_, ?_, hotypes, ?_, ?_⟩
  · change (LIR.program.runBlock (dialect code)
      ⟨.l103f00, args, fr.original⟩).next (dialect code) [] = .done output
    rw [hblock]
    rfl
  · rw [htag, hstore, hreturn]
  · change output.values[4] = ⟨64, fr.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, fr.rbx⟩ ∧ output.values[5] = ⟨64, fr.rbp⟩ ∧
      output.values[12] = ⟨64, fr.r12⟩ ∧ output.values[13] = ⟨64, fr.r13⟩ ∧
      output.values[14] = ⟨64, fr.r14⟩ ∧ output.values[15] = ⟨64, fr.r15⟩ ∧
      output.values[39] = ⟨32, fr.mxcsr⟩ ∧ output.values[50] = ⟨16, fr.ftw⟩ ∧
      output.values[51] = ⟨16, fr.fcw⟩ ∧ True
    exact ⟨ho4, ho22.trans hdf, ho3.trans hbx, ho5.trans hbp, ho12.trans h12,
      ho13.trans h13, ho14.trans h14, ho15.trans h15, ho39.trans h39, ho50.trans h50, ho51.trans h51, trivial⟩
  · rw [hfinalStore]
    unfold memCopy
    apply (RamWriteFrame.refl fr.original _).memStore
    refine ⟨span fr.rdi fr.rdx.toNat, by simp, ?_⟩
    change fr.rdi.toNat ≤ fr.rdi.toNat ∧
      fr.rdi.toNat + 8 * fr.rdx.toNat / 8 ≤ fr.rdi.toNat + fr.rdx.toNat ∧
      fr.rdi.toNat + 8 * fr.rdx.toNat / 8 ≤ 2^64
    have := hw.readable.low
    constructor
    · exact Nat.le_refl _
    · constructor <;> omega
  · intro i hi
    rw [hfinalStore, memCopy_getElem?_self _ _ _ _ (by have := hr.low; omega) i hi]
    obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.mp (hr.present i hi)
    simp only [memByte, PhysicalMemory.read, hb, Option.getD_some]

end AesGcm.Proofs.Machine.Runtime
