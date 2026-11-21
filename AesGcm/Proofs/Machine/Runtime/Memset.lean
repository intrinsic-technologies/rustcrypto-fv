import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.LIR.Fn103eb0.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Machine.Runtime.Partition
import AesGcm.Proofs.Copied.X86Proofs.Lift.Rep
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Proofs.Machine.Runtime Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

private theorem memset_zero_returns_of_guards (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (dst count rsp : BitVec 64)
    (hdst : args[7].get 64 = dst) (hc : args[2].get 64 = count)
    (hz : args[6].get 64 = 0) (hsp : args[4].get 64 = rsp)
    (hdf : args[22].get 1 = 0) (htypes : GPRsTyped args)
    (hmask : ((-(dst.setWidth 32)) &&& 7).setWidth 64 = 0)
    (htail : ((count.setWidth 32 &&& 7).setWidth 64) = 0)
    (hw : RepStosOk code mem 0 dst (count >>> 3) 8 0x103ee9 3)
    (hret : LoadOk (memFill mem dst (0 : BitVec 64) (count >>> 3).toNat) rsp 8 ∧
      (memLoad (memFill mem dst (0 : BitVec 64) (count >>> 3).toNat) rsp 64).toNat < 2^32) :
    ∃ output, LIR.program.runBlock (dialect code) ⟨.l103eb0, args, mem⟩ = .returned output ∧
      output.store = memFill mem dst (0 : BitVec 64) (count >>> 3).toNat ∧
      output.tag = some ⟨64, memLoad output.store rsp 64⟩ ∧
      output.values[0] = ⟨64, dst⟩ ∧ output.values[4] = ⟨64, rsp + 8⟩ ∧
      output.values[3] = args[3] ∧ output.values[5] = args[5] ∧
      output.values[12] = args[12] ∧ output.values[13] = args[13] ∧
      output.values[14] = args[14] ∧ output.values[15] = args[15] ∧
      output.values[22] = args[22] ∧
      output.values[39] = args[39] ∧ output.values[50] = args[50] ∧
      output.values[51] = args[51] ∧ GPRsTyped output.values := by
  have hfillzero (m : Ram) (a : BitVec 64) (v : BitVec 8) : memFill m a v 0 = m := rfl
  have hcmp (a : BitVec 64) : (cmpSpec a 0).CF = false := by
    simp [cmpSpec, subSpec]
  have hsub0 (a : BitVec 64) : a - 0 = a := BitVec.sub_zero a
  have hadd0 (a : BitVec 64) : a + 0 = a := BitVec.add_zero a
  cfg_eval [hdst, hc, hz, hsp, hdf, hmask, hcmp]
  simp (config := { bitVecOfNat := false }) only [hmask, hcmp,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat, BitVec.reduceOfNat,
    hsub0, hadd0, hfillzero, htail, true_or, hw, or_true, hret]
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



def memsetZeroPre (code : CodeMap) (fr : Activation) (mem : Ram) : Prop :=
  fr.rsi = 0 ∧ fr.rdi.toNat % 8 = 0 ∧ fr.rdx.toNat % 8 = 0 ∧
    Writable code mem fr.rdi fr.rdx.toNat ∧ RangeApart fr.rdi fr.rdx.toNat fr.rsp 8

theorem memset_zero_call (code : CodeMap)
    (hcode : ∀ x ∈ codeRange 0x103ee9 [0xF3, 0x48, 0xAB], x ∈ code) :
    CallContract LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
      (fun fr => [span fr.rdi fr.rdx.toNat]) (memsetZeroPre code)
      (fun fr mem => ∀ i < fr.rdx.toNat, mem[fr.rdi + BitVec.ofNat 64 i]? = some 0) := by
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
  rcases hpre with ⟨hzero, halign, hlen, hw, hap⟩
  have hq : 8 * (fr.rdx >>> 3).toNat = fr.rdx.toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have hmask : ((-(fr.rdi.setWidth 32)) &&& 7).setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    change (alignmentBytes fr.rdi).toNat = 0
    rw [alignmentBytes_toNat, halign]
  have htail : ((fr.rdx.setWidth 32 &&& 7).setWidth 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
    change ((fr.rdx.setWidth 32).toNat &&& (2^3 - 1)) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^32), hlen]
  have hwq : Writable code fr.original fr.rdi (8 * (fr.rdx >>> 3).toNat) := by
    simpa only [hq] using hw
  have hguard := repStosOk_of_region hwq (df := 0) rfl hcode
  have hwidth : 64 * (fr.rdx >>> 3).toNat / 8 = fr.rdx.toNat := by omega
  have hreturn : memLoad (memFill fr.original fr.rdi (0 : BitVec 64)
      (fr.rdx >>> 3).toNat) fr.rsp 64 = fr.ret := by
    unfold memFill
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (by simpa only [hwidth] using hap), hv]
  have hread := hr.memStore fr.rdi ((0 : BitVec 64).replicate (fr.rdx >>> 3).toNat)
  obtain ⟨output, hblock, hstore, htag, ho0, ho4, ho3, ho5, ho12, ho13, ho14, ho15, ho22, ho39, ho50, ho51, hotypes⟩ :=
    memset_zero_returns_of_guards code args fr.original fr.rdi fr.rdx fr.rsp
      (by rw [hdst]; rfl) (by rw [hc]; rfl) (by rw [hz, hzero]; rfl)
      (by rw [hsp]; rfl) (by rw [hdf]; rfl) htypes hmask htail hguard
      ⟨⟨hread.low, hread.present⟩, by rw [hreturn]; exact hretlow⟩
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
      ho13.trans h13, ho14.trans h14, ho15.trans h15, ho39.trans h39, ho50.trans h50, ho51.trans h51, trivial⟩
  · rw [hstore]
    unfold memFill
    apply (RamWriteFrame.refl fr.original _).memStore
    refine ⟨span fr.rdi fr.rdx.toNat, by simp, ?_⟩
    change fr.rdi.toNat ≤ fr.rdi.toNat ∧
      fr.rdi.toNat + 64 * (fr.rdx >>> 3).toNat / 8 ≤ fr.rdi.toNat + fr.rdx.toNat ∧
      fr.rdi.toNat + 64 * (fr.rdx >>> 3).toNat / 8 ≤ 2^64
    have := hw.readable.low
    constructor
    · exact Nat.le_refl _
    · constructor <;> omega
  · intro i hi
    rw [hstore]
    unfold memFill
    rw [memStore_getElem?_self_of_le _ _ _ (by omega) i (by omega),
      storedByte_replicate (0 : BitVec 64) (by decide) (fr.rdx >>> 3).toNat i (by omega)]
    change some (UInt8.ofNat (0 >>> (8 * (i % 8)))) = some 0
    rw [Nat.zero_shiftRight]
    rfl

set_option maxHeartbeats 2000000 in
theorem memset_zero_exec (code : CodeMap)
    (hcode : ∀ x ∈ codeRange 0x103ee9 [0xF3, 0x48, 0xAB], x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (dst count rsp ret : BitVec 64)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hdst : args[7].get 64 = dst) (hcount : args[2].get 64 = count)
    (hzero : args[6].get 64 = 0) (hsp : args[4].get 64 = rsp)
    (hdf : args[22] = ⟨1, 0⟩)
    (hread : Readable mem rsp 8) (hret : memLoad mem rsp 64 = ret)
    (hretLow : ret.toNat < 2^32) (halign : rsp.toNat % 16 = 8)
    (hw : Writable code mem dst count.toNat)
    (hdstAlign : dst.toNat % 8 = 0) (hcountAlign : count.toNat % 8 = 0)
    (hapart : RangeApart dst count.toNat rsp 8) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨⟨.l103eb0, args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, ret⟩ ∧
      output.values[4] = ⟨64, rsp + 8⟩ ∧
      output.values[3] = args[3] ∧ output.values[5] = args[5] ∧
      output.values[12] = args[12] ∧ output.values[13] = args[13] ∧
      output.values[14] = args[14] ∧ output.values[15] = args[15] ∧
      output.values[22] = args[22] ∧ GPRsTyped output.values ∧
      RamWriteFrame mem output.store [span dst count.toNat] ∧
      (∀ i < count.toNat, output.store[dst + BitVec.ofNat 64 i]? = some 0) := by
  let fr : Activation := {
    original := mem, rsp := args[4].get 64, ret := ret, low := args[4].get 64,
    rbx := args[3].get 64, rbp := args[5].get 64,
    r12 := args[12].get 64, r13 := args[13].get 64,
    r14 := args[14].get 64, r15 := args[15].get 64,
    rdi := args[7].get 64, rsi := args[6].get 64, rdx := args[2].get 64,
    rcx := args[1].get 64, r8 := args[8].get 64, r9 := args[9].get 64,
    mxcsr := args[39].get 32, ftw := args[50].get 16, fcw := args[51].get 16, fs := default }
  have hentry : Atom.All code args mem (LIR.Fn103eb0.frameInfo.entryAtoms fr) := by
    apply frame_entryAtoms
    · rintro ⟨r, hr⟩ hin
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      all_goals exact htypes.value ⟨_, by decide⟩
    · exact h39
    · exact h50
    · exact h51
    · exact hdf
    · change Readable mem (args[4].get 64) 8
      rw [hsp]
      exact hread
    · change memLoad mem (args[4].get 64) 64 = ret
      rw [hsp]
      exact hret
    · exact hretLow
    · intro hwindow
      change 0 < 0 at hwindow
      omega
    · change (args[4].get 64).toNat + 0 ≤ (args[4].get 64).toNat
      omega
    · change (args[4].get 64).toNat % 16 = 8
      rw [hsp]
      exact halign
    · trivial
  have hpre : memsetZeroPre code fr mem := by
    change args[6].get 64 = 0 ∧ (args[7].get 64).toNat % 8 = 0 ∧
      (args[2].get 64).toNat % 8 = 0 ∧
      Writable code mem (args[7].get 64) (args[2].get 64).toNat ∧
      RangeApart (args[7].get 64) (args[2].get 64).toNat (args[4].get 64) 8
    rw [hdst, hcount, hsp]
    exact ⟨hzero, hdstAlign, hcountAlign, hw, hapart⟩
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hbytes⟩ :=
    memset_zero_call code hcode fr ⟨.l103eb0, args, mem⟩ rfl rfl hentry htypes hpre
  change output.values[4] = ⟨64, fr.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
    output.values[3] = ⟨64, fr.rbx⟩ ∧ output.values[5] = ⟨64, fr.rbp⟩ ∧
    output.values[12] = ⟨64, fr.r12⟩ ∧ output.values[13] = ⟨64, fr.r13⟩ ∧
    output.values[14] = ⟨64, fr.r14⟩ ∧ output.values[15] = ⟨64, fr.r15⟩ ∧
      output.values[39] = ⟨32, fr.mxcsr⟩ ∧ output.values[50] = ⟨16, fr.ftw⟩ ∧
      output.values[51] = ⟨16, fr.fcw⟩ ∧ True at hdone
  rcases hdone with ⟨h4, h22, h3, h5, h12, h13, h14, h15, -, -, -, -⟩
  have hspOut : output.values[4] = ⟨64, rsp + 8⟩ := by
    simpa only [fr, hsp] using h4
  have hframeOut : RamWriteFrame mem output.store [span dst count.toNat] := by
    constructor
    · intro address hout
      apply hframe.outside address
      refine ⟨hout.1, ?_⟩
      intro region hregion
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hregion
      rcases hregion with rfl | rfl
      · change address.toNat + 1 ≤ (args[4].get 64).toNat ∨
          (args[4].get 64).toNat +
            ((args[4].get 64).toNat - (args[4].get 64).toNat) ≤ address.toNat
        omega
      · simpa only [fr, hdst, hcount] using hout.2 (span dst count.toNat) (by simp)
    · exact hframe.present
  refine ⟨output, hexec, htag, hspOut, ?_, ?_, ?_, ?_, ?_, ?_, h22.trans hdf.symm,
    houtTypes, hframeOut, ?_⟩
  · exact h3.trans (htypes.value ⟨3, by decide⟩).symm
  · exact h5.trans (htypes.value ⟨5, by decide⟩).symm
  · exact h12.trans (htypes.value ⟨12, by decide⟩).symm
  · exact h13.trans (htypes.value ⟨13, by decide⟩).symm
  · exact h14.trans (htypes.value ⟨14, by decide⟩).symm
  · exact h15.trans (htypes.value ⟨15, by decide⟩).symm
  · simpa only [fr, hdst, hcount] using hbytes

end AesGcm.Proofs.Machine.Runtime
