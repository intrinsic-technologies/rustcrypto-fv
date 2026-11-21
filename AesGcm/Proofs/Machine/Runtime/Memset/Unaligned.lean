import AesGcm.Proofs.Machine.Runtime.Memset

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

private theorem zero_replicate (w c : Nat) : (0 : BitVec w).replicate c = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_replicate]

private theorem zeroFill_getElem?_self (mem : Ram) (dst : BitVec 64) (c : Nat)
    (hlen : c ≤ 2^64) (i : Nat) (hi : i < c) :
    (memFill mem dst (0 : BitVec 8) c)[dst + BitVec.ofNat 64 i]? = some 0 := by
  unfold memFill
  rw [zero_replicate, memStore_getElem?_self_of_le mem dst _ (by omega) i (by omega)]
  change some (UInt8.ofNat (0 >>> (8 * i))) = some 0
  rw [Nat.zero_shiftRight]
  rfl

private theorem zeroFill_getElem?_of_ne (mem : Ram) (dst x : BitVec 64) (c : Nat)
    (hx : ∀ i < c, dst + BitVec.ofNat 64 i ≠ x) :
    (memFill mem dst (0 : BitVec 8) c)[x]? = mem[x]? := by
  exact memStore_getElem?_of_ne mem dst _ x (by
    intro i hi
    exact hx i (by omega))

private theorem zeroFill_qword (mem : Ram) (dst : BitVec 64) (c : Nat) :
    memFill mem dst (0 : BitVec 64) c = memFill mem dst (0 : BitVec 8) (8 * c) := by
  unfold memFill
  rw [zero_replicate, zero_replicate]
  exact congrArg (fun w ↦ memStore mem dst (0 : BitVec w)) (by omega : 64 * c = 8 * (8 * c))

private theorem zeroFill_append (mem : Ram) (dst : BitVec 64) (h q : Nat)
    (hlen : h + q ≤ 2^64) :
    memFill (memFill mem dst (0 : BitVec 8) h)
      (dst + BitVec.ofNat 64 h) (0 : BitVec 8) q =
      memFill mem dst (0 : BitVec 8) (h + q) := by
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hq : ∃ j < q, dst + BitVec.ofNat 64 h + BitVec.ofNat 64 j = x
  · obtain ⟨j, hj, rfl⟩ := hq
    rw [zeroFill_getElem?_self _ _ q (by omega) j hj]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [zeroFill_getElem?_self _ _ (h + q) hlen (h + j) (by omega)]
  · rw [zeroFill_getElem?_of_ne _ _ x q (by
      intro j hj he
      exact hq ⟨j, hj, he⟩)]
    by_cases hh : ∃ i < h, dst + BitVec.ofNat 64 i = x
    · obtain ⟨i, hi, rfl⟩ := hh
      rw [zeroFill_getElem?_self _ _ h (by omega) i hi,
        zeroFill_getElem?_self _ _ (h + q) hlen i (by omega)]
    · rw [zeroFill_getElem?_of_ne _ _ x h (by
        intro i hi he
        exact hh ⟨i, hi, he⟩)]
      symm
      apply zeroFill_getElem?_of_ne
      intro i hi he
      by_cases ih : i < h
      · exact hh ⟨i, ih, he⟩
      · apply hq
        refine ⟨i - h, by omega, ?_⟩
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
          Nat.add_sub_of_le (by omega : h ≤ i)] using he

private theorem memset_unaligned_returns_of_guards (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (dst count rsp : BitVec 64)
    (hdst : args[7].get 64 = dst) (hz : args[6].get 64 = 0)
    (hc : args[2].get 64 = count) (hsp : args[4].get 64 = rsp)
    (hdf : args[22].get 1 = 0) (htypes : GPRsTyped args) :
    let h := prefixBytes dst count
    let q := (count - h) >>> 3
    let t := ((count - h).setWidth 32 &&& 7).setWidth 64
    let mem₁ := memFill mem dst (0 : BitVec 8) h.toNat
    let mem₂ := memFill mem₁ (dst + BitVec.ofNat 64 h.toNat) (0 : BitVec 64) q.toNat
    let mem₃ := memFill mem₂ (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (0 : BitVec 8) t.toNat
    RepStosOk code mem 0 dst h 1 0x103ee4 2 →
    RepStosOk code mem₁ 0 (dst + BitVec.ofNat 64 h.toNat) q 8 0x103ee9 3 →
    RepStosOk code mem₂ 0
      (dst + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) t 1 0x103eef 2 →
    (LoadOk mem₃ rsp 8 ∧ (memLoad mem₃ rsp 64).toNat < 2^32) →
    ∃ output, LIR.program.runBlock (dialect code) ⟨.l103eb0, args, mem⟩ = .returned output ∧
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
  cfg_eval [LIR.program, hdst, hz, hc, hsp, hdf, hprefix]
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

theorem memset_zero_call_of_writable (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat])
      (fun fr mem ↦ fr.rsi = 0 ∧ Writable code mem fr.rdi fr.rdx.toNat ∧
        RangeApart fr.rdi fr.rdx.toNat fr.rsp 8)
      (fun fr mem ↦ ∀ i < fr.rdx.toNat, mem[fr.rdi + BitVec.ofNat 64 i]? = some 0) := by
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
  rcases hentry with ⟨hsp, hdf, -, hc, hbx, hbp, hz, hdst, -, -, h12, h13, h14, h15, h39, h50, h51,
    hr, hv, hretlow, -, -, -⟩
  rcases hpre with ⟨hzero, hw, hapret⟩
  let h := prefixBytes fr.rdi fr.rdx
  let q := (fr.rdx - h) >>> 3
  let t := ((fr.rdx - h).setWidth 32 &&& 7).setWidth 64
  let mem₁ := memFill fr.original fr.rdi (0 : BitVec 8) h.toNat
  let mem₂ := memFill mem₁ (fr.rdi + BitVec.ofNat 64 h.toNat) (0 : BitVec 64) q.toNat
  let mem₃ := memFill mem₂
    (fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
    (0 : BitVec 8) t.toNat
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
  have hcode₁ : ∀ x ∈ codeRange 0x103ee4 [0xF3, 0xAA], x ∈ code := by
    intro x hx
    exact hcode x (LIR.code_l103eb0 x (codeRange_mem_of_drop (p := 0x103eb0)
      (all := LIR.bytes_l103eb0) 52 (by decide +kernel) x hx))
  have hcode₂ : ∀ x ∈ codeRange 0x103ee9 [0xF3, 0x48, 0xAB], x ∈ code := by
    intro x hx
    exact hcode x (LIR.code_l103eb0 x (codeRange_mem_of_drop (p := 0x103eb0)
      (all := LIR.bytes_l103eb0) 57 (by decide +kernel) x hx))
  have hcode₃ : ∀ x ∈ codeRange 0x103eef [0xF3, 0xAA], x ∈ code := by
    intro x hx
    exact hcode x (LIR.code_l103eb0 x (codeRange_mem_of_drop (p := 0x103eb0)
      (all := LIR.bytes_l103eb0) 63 (by decide +kernel) x hx))
  have hfirst := repStosOk_of_region
    (hw.sub (Nat.le_refl _) (by omega) : Writable code fr.original fr.rdi (1 * h.toNat))
    (df := 0) rfl hcode₁
  have hw₁ : Writable code mem₁ fr.rdi fr.rdx.toNat :=
    hw.memStore fr.rdi ((0 : BitVec 8).replicate h.toNat)
  have hmDst : (fr.rdi + BitVec.ofNat 64 h.toNat).toNat = fr.rdi.toNat + h.toNat :=
    hdNat _ (by omega)
  have hmiddle := repStosOk_of_region
    (hw₁.sub (a := fr.rdi + BitVec.ofNat 64 h.toNat) (by omega) (by omega) :
      Writable code mem₁ (fr.rdi + BitVec.ofNat 64 h.toNat) (8 * q.toNat))
    (df := 0) rfl hcode₂
  have hw₂ : Writable code mem₂ fr.rdi fr.rdx.toNat :=
    hw₁.memStore (fr.rdi + BitVec.ofNat 64 h.toNat) ((0 : BitVec 64).replicate q.toNat)
  have htDst : (fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)).toNat =
      fr.rdi.toNat + h.toNat + 8 * q.toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hdNat _ (by omega)]
    omega
  have hlast := repStosOk_of_region
    (hw₂.sub (a := fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat))
      (by omega) (by omega) : Writable code mem₂
        (fr.rdi + BitVec.ofNat 64 h.toNat + BitVec.ofNat 64 (8 * q.toNat)) (1 * t.toNat))
    (df := 0) rfl hcode₃
  have hfill : mem₃ = memFill fr.original fr.rdi (0 : BitVec 8) fr.rdx.toNat := by
    dsimp only [mem₃, mem₂, mem₁]
    rw [zeroFill_qword, zeroFill_append _ _ _ _ (by have := hw.readable.low; omega)]
    rw [zeroFill_append _ _ _ _ (by have := hw.readable.low; omega), ← Nat.add_assoc, htotal]
  have hreturn : memLoad mem₃ fr.rsp 64 = fr.ret := by
    rw [hfill]
    unfold memFill
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (by
      simpa only [show 8 * fr.rdx.toNat / 8 = fr.rdx.toNat by omega] using hapret), hv]
  have hread : Readable mem₃ fr.rsp 8 := by
    rw [hfill]
    exact hr.memStore fr.rdi ((0 : BitVec 8).replicate fr.rdx.toNat)
  obtain ⟨output, hblock, hstore, htag, ho0, ho4, ho3, ho5, ho12, ho13, ho14, ho15,
      ho22, ho39, ho50, ho51, hotypes⟩ :=
    memset_unaligned_returns_of_guards code args fr.original fr.rdi fr.rdx fr.rsp
      (by rw [hdst]; rfl) (by rw [hz, hzero]; rfl) (by rw [hc]; rfl)
      (by rw [hsp]; rfl) (by rw [hdf]; rfl) htypes hfirst hmiddle hlast
      ⟨⟨hread.low, hread.present⟩, by rw [hreturn]; exact hretlow⟩
  have hfinalStore : output.store = memFill fr.original fr.rdi (0 : BitVec 8) fr.rdx.toNat :=
    (show output.store = mem₃ from hstore).trans hfill
  refine ⟨output, .done ?_, ?_, ?_, hotypes, ?_, ?_⟩
  · change (LIR.program.runBlock (dialect code)
      ⟨.l103eb0, args, fr.original⟩).next (dialect code) [] = .done output
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
      ho13.trans h13, ho14.trans h14, ho15.trans h15,
      ho39.trans h39, ho50.trans h50, ho51.trans h51, trivial⟩
  · rw [hfinalStore]
    unfold memFill
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
    rw [hfinalStore]
    exact zeroFill_getElem?_self _ _ _ (by have := hw.readable.low; omega) i hi


end AesGcm.Proofs.Machine.Runtime
