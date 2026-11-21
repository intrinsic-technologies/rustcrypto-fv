import AesGcm.Proofs.AES16.KeySchedule.Columns16
import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Copied.X86Proofs.Refine.Tactic
import AesGcm.Proofs.Machine.LIR.Fn104010.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open X86Proofs.CFG
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private def columnMachineRk (previous substituted : BitVec 16) (rotation : BitVec 64) : BitVec 64 :=
  let rotated := mergeGPR 16
    (substituted.rotateRight (shiftCount 16 ((rotation.setWidth 32).setWidth 8)))
    (substituted.setWidth 64)
  let masked := ((rotated.setWidth 32) &&& 0x1111).setWidth 64
  mergeGPR 16 (masked.setWidth 16 ^^^ previous) masked

private def columnMachineWord (previous substituted : BitVec 16) (rotation : BitVec 64) : BitVec 16 :=
  let rk := columnMachineRk previous substituted rotation
  (((((rk <<< 3).setWidth 32) &&& 0xffff8888) ^^^ rk.setWidth 32) ^^^
    ((((rk <<< 2).setWidth 32) &&& 0xffffcccc) ^^^
      ((rk + rk).setWidth 32 &&& 0xffffeeee))).setWidth 16

private theorem columnMachineWord_eq (previous substituted : BitVec 16) (rotation : BitVec 64)
    (hrot : rotation.toNat < 16) :
    columnMachineWord previous substituted rotation =
      xorColumnsWord previous substituted rotation.toNat := by
  have hcount : shiftCount 16 ((rotation.setWidth 32).setWidth 8) = rotation.toNat := by
    simp only [shiftCount, show (16 : Nat) ≠ 64 by decide, ite_false, BitVec.toNat_setWidth]
    omega
  simp only [columnMachineWord, BitVec.setWidth_xor, BitVec.setWidth_and,
    BitVec.setWidth_shiftLeft_of_le (by decide : 16 ≤ 64),
    BitVec.setWidth_add _ _ (by decide : 16 ≤ 64),
    columnMachineRk, AesGcm.Proofs.setWidth_mergeGPR16,
    BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), hcount]
  let x := substituted.rotateRight rotation.toNat &&& (0x1111 : BitVec 16) ^^^ previous
  change (x <<< 3 &&& 0x8888 ^^^ x) ^^^
    (x <<< 2 &&& 0xcccc ^^^ (x+x) &&& 0xeeee) = _
  have hrk : previous ^^^ (0x1111 &&& substituted.rotateRight rotation.toNat) = x := by
    dsimp only [x]
    rw [BitVec.and_comm]
    exact BitVec.xor_comm _ _
  have hdouble : x + x = x <<< 1 := by bv_omega
  dsimp only [xorColumnsWord]
  rw [hrk, hdouble]
  simp only [BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem xorColumns_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x104010 862 := by
  have hhelperCode : ∀ x ∈ codeRange 0x104010
      (LIR.textSection.bytes.toList.drop 0x4010 |>.take 862), x ∈ LIR.fnCode :=
    codeRange_sub_section (s := LIR.textSection) (.head _) 0x4010 862 (by decide +kernel)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl
  have hx := storeOk_of_codeRange h (fun x hx => hcode x (hhelperCode x hx))
  have hlen : (LIR.textSection.bytes.toList.drop 0x4010 |>.take 862).length = 862 := by
    decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option maxHeartbeats 1500000 in
theorem xorColumns_callContract (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l104010 LIR.Fn104010.frameInfo
      (fun fr ↦ [span (fr.rdi + BitVec.ofNat 64 (2 * fr.rdx.toNat)) 16])
      (fun fr mem ↦ Writable code mem fr.rdi (2 * fr.rsi.toNat) ∧
        fr.rsi.toNat ≤ 120 ∧ 8 ≤ fr.rcx.toNat ∧ fr.rcx.toNat ≤ fr.rdx.toNat ∧
        fr.rdx.toNat + 8 ≤ fr.rsi.toNat ∧ fr.r8.toNat < 16 ∧
        (callStack fr).Disjoint (span fr.rdi (2 * fr.rsi.toNat)))
      (fun fr mem ↦ ∀ p : Fin 8,
        memLoad mem (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p.val))) 16 =
          xorColumnsWord
            (memLoad fr.original
              (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat - fr.rcx.toNat + p.val))) 16)
            (memLoad fr.original
              (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p.val))) 16)
            fr.r8.toNat) := by
  dsimp only [CallContract, LIR.lifted]
  intro fr ⟨lab, args, mem⟩ hl hs hf hTypes hpre
  dsimp only at hl hs hf hTypes hpre
  subst lab mem
  rcases hpre with ⟨hWrite, hn, hbackMin, hback, hoff, hrot, hApart⟩
  have hRead := hWrite.readable
  revert hf hTypes
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hf
  change a4 = ⟨64, fr.rsp⟩ ∧ a22 = ⟨1, 0⟩ ∧ a1 = ⟨64, fr.rcx⟩ ∧
    a2 = ⟨64, fr.rdx⟩ ∧ a3 = ⟨64, fr.rbx⟩ ∧ a5 = ⟨64, fr.rbp⟩ ∧
    a6 = ⟨64, fr.rsi⟩ ∧ a7 = ⟨64, fr.rdi⟩ ∧ a8 = ⟨64, fr.r8⟩ ∧ a9 = ⟨64, fr.r9⟩ ∧
    a12 = ⟨64, fr.r12⟩ ∧ a13 = ⟨64, fr.r13⟩ ∧ a14 = ⟨64, fr.r14⟩ ∧ a15 = ⟨64, fr.r15⟩ ∧
    a39 = ⟨32, fr.mxcsr⟩ ∧ a50 = ⟨16, fr.ftw⟩ ∧ a51 = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 144) 144 ∧
    fr.low.toNat + 144 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
    Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
    Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
    (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True at hf
  rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    h39, h50, h51, hRetRead, hRet, hRetLow, hStack, hRoom, hAlign, -⟩
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
  have hRetReadLow := hRetRead.low
  have hApartNum : fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 2 * fr.rsi.toNat ≤ fr.low.toNat := by
    have h := hApart (max fr.low.toNat fr.rdi.toNat)
    simp only [callStack, span, MemoryRegion.Disjoint, MemoryRegion.Contains] at hApart
    dsimp only [callStack, span, MemoryRegion.Contains] at h
    omega
  have hbranch (k : Nat) (hk : k < 8) :
      (!(cmpSpec (fr.rdx + BitVec.ofNat 64 k) fr.rsi).CF) = false := by
    have hlt : (fr.rdx + BitVec.ofNat 64 k).toNat < fr.rsi.toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [cmpSpec, subSpec, hlt, decide_true, Bool.not_true]
  have hprevbranch (k : Nat) (hk : k < 8) :
      (!(cmpSpec (fr.rdx + BitVec.ofNat 64 k - fr.rcx) fr.rsi).CF) = false := by
    have ha' : (fr.rdx + BitVec.ofNat 64 k).toNat = fr.rdx.toNat + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlt : (fr.rdx + BitVec.ofNat 64 k - fr.rcx).toNat < fr.rsi.toNat := by
      rw [BitVec.toNat_sub_of_le (show fr.rcx ≤ fr.rdx + BitVec.ofNat 64 k from
        (show fr.rcx.toNat ≤ (fr.rdx + BitVec.ofNat 64 k).toNat by omega)), ha']
      omega
    simp only [cmpSpec, subSpec, hlt, decide_true, Bool.not_true]
  have hb0 := hbranch 0 (by decide)
  have hp0 := hprevbranch 0 (by decide)
  simp only [BitVec.add_zero] at hb0 hp0
  have hhelperApart := @xorColumns_rangeApart code hcode
  have hsub : (fr.rdx - fr.rcx).toNat = fr.rdx.toNat - fr.rcx.toNat :=
    BitVec.toNat_sub_of_le (show fr.rcx ≤ fr.rdx from hback)
  have haddr (index : BitVec 64) (k : Nat)
      (h : fr.rdi.toNat + 2 * (index.toNat + k) < 2^64) :
      (fr.rdi + (index <<< 1) + BitVec.ofNat 64 (2*k)).toNat =
        fr.rdi.toNat + 2 * (index.toNat + k) := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := index.toNat * 2^1) (by omega),
      Nat.mod_eq_of_lt (a := fr.rdi.toNat + index.toNat * 2^1) (by omega),
      Nat.mod_eq_of_lt (a := 2*k) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have ha (k : Nat) (hk : k ≤ 8) :
      (fr.rdi + (fr.rdx <<< 1) + BitVec.ofNat 64 (2*k)).toNat =
        fr.rdi.toNat + 2 * (fr.rdx.toNat + k) := haddr _ _ (by omega)
  have hb (k : Nat) (hk : k ≤ 8) :
      (fr.rdi + ((fr.rdx-fr.rcx) <<< 1) + BitVec.ofNat 64 (2*k)).toNat =
        fr.rdi.toNat + 2 * (fr.rdx.toNat-fr.rcx.toNat + k) := by
    simpa only [hsub] using haddr (fr.rdx-fr.rcx) k (by rw [hsub]; omega)
  have hDest : Writable code fr.original (fr.rdi + (fr.rdx <<< 1)) 16 := by
    apply hWrite.sub
    all_goals have h := ha 0 (by decide); simp only [Nat.mul_zero, BitVec.add_zero, Nat.add_zero] at h; rw [h]; omega
  have hDestRead := hDest.readable
  have hPrev : Readable fr.original (fr.rdi + ((fr.rdx-fr.rcx) <<< 1)) 16 := by
    apply hRead.sub
    all_goals have h := hb 0 (by decide); simp only [Nat.mul_zero, BitVec.add_zero, Nat.add_zero] at h; rw [h]; omega
  have hindexed (k : Nat) :
      fr.rdi + ((fr.rdx + BitVec.ofNat 64 k-fr.rcx) <<< 1) =
      fr.rdi + ((fr.rdx-fr.rcx) <<< 1) + BitVec.ofNat 64 (2*k) := by
    have h : fr.rdx + BitVec.ofNat 64 k-fr.rcx = (fr.rdx-fr.rcx) + BitVec.ofNat 64 k := by
      bv_omega
    have hc : BitVec.ofNat 64 k <<< 1 = BitVec.ofNat 64 (2*k) := by
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      change BitVec.ofNat 64 k * BitVec.ofNat 64 2 = _
      rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]
    have hc : BitVec.ofNat 64 k <<< 1 = BitVec.ofNat 64 (2*k) := by
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      change BitVec.ofNat 64 k * BitVec.ofNat 64 2 = _
      rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]
    rw [h, BitVec.shiftLeft_add_distrib, hc, BitVec.add_assoc]
  have hb1 := hbranch 1 (by decide)
  have hp1 := hprevbranch 1 (by decide)
  have hb2 := hbranch 2 (by decide)
  have hp2 := hprevbranch 2 (by decide)
  have hb3 := hbranch 3 (by decide)
  have hp3 := hprevbranch 3 (by decide)
  have hb4 := hbranch 4 (by decide)
  have hp4 := hprevbranch 4 (by decide)
  have hb5 := hbranch 5 (by decide)
  have hp5 := hprevbranch 5 (by decide)
  have hb6 := hbranch 6 (by decide)
  have hp6 := hprevbranch 6 (by decide)
  have hb7 := hbranch 7 (by decide)
  have hp7 := hprevbranch 7 (by decide)
  let a (k : Nat) := if k = 0 then fr.rdi + (fr.rdx <<< 1) else fr.rdi + (fr.rdx <<< 1) + BitVec.ofNat 64 (2*k)
  let b (k : Nat) := if k = 0 then fr.rdi + ((fr.rdx-fr.rcx) <<< 1) else fr.rdi + ((fr.rdx-fr.rcx) <<< 1) + BitVec.ofNat 64 (2*k)
  let word (m : Ram) (k : Nat) := columnMachineWord (memLoad m (b k) 16)
    (memLoad m (a k) 16) fr.r8
  let m0 := memStore fr.original (fr.rsp - 8) (a0.get 64)
  have haEq (k : Nat) : a k = fr.rdi + (fr.rdx <<< 1) + BitVec.ofNat 64 (2*k) := by
    dsimp only [a]
    split
    · rename_i hk
      subst k
      simp only [Nat.mul_zero, BitVec.add_zero]
    · rfl
  have hbEq (k : Nat) : b k = fr.rdi + ((fr.rdx-fr.rcx) <<< 1) + BitVec.ofNat 64 (2*k) := by
    dsimp only [b]
    split
    · rename_i hk
      subst k
      simp only [Nat.mul_zero, BitVec.add_zero]
    · rfl
  have ha' (k : Nat) (hk : k ≤ 8) :
      (a k).toNat = fr.rdi.toNat + 2 * (fr.rdx.toNat + k) := by rw [haEq]; exact ha k hk
  have hb' (k : Nat) (hk : k ≤ 8) :
      (b k).toNat = fr.rdi.toNat + 2 * (fr.rdx.toNat-fr.rcx.toNat+k) := by rw [hbEq]; exact hb k hk
  have hcanonical (index : BitVec 64) (k : Nat)
      (h : fr.rdi.toNat + 2 * (index.toNat + k) < 2^64) :
      fr.rdi + (index <<< 1) + BitVec.ofNat 64 (2*k) =
        fr.rdi + BitVec.ofNat 64 (2*(index.toNat+k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [haddr index k h]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2*(index.toNat+k)) (by omega), Nat.mod_eq_of_lt h]
  have hAddrA (k : Nat) (hk : k ≤ 8) : a k =
      fr.rdi + BitVec.ofNat 64 (2*(fr.rdx.toNat+k)) := by
    rw [haEq]
    exact hcanonical fr.rdx k (by omega)
  have hAddrB (k : Nat) (hk : k ≤ 8) : b k =
      fr.rdi + BitVec.ofNat 64 (2*(fr.rdx.toNat-fr.rcx.toNat+k)) := by
    rw [hbEq, ← hsub]
    exact hcanonical (fr.rdx-fr.rcx) k (by rw [hsub]; omega)
  have hsp8 : (fr.rsp-8).toNat = fr.rsp.toNat-8 := by
    rw [BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ fr.rsp from (show 8 ≤ fr.rsp.toNat by omega))]
    rfl
  have hslot8 : InRegions [fr.region] (fr.rsp-8) 8 := by
    refine ⟨fr.region, by simp, ?_⟩
    simp only [InRegion, Activation.region, hsp8]
    omega
  have hfs : RamWriteFrame fr.original m0 [fr.region] :=
    (RamWriteFrame.refl _ _).memStore (a0.get 64) hslot8
  have hsavedSource (x : BitVec 64) (hx : fr.rdi.toNat ≤ x.toNat)
      (hx' : x.toNat + 2 ≤ fr.rdi.toNat + 2 * fr.rsi.toNat) :
      memLoad m0 x 16 = memLoad fr.original x 16 := by
    apply hfs.memLoad_eq
    refine ⟨Nat.le_trans hx' (Nat.le_trans hReadLow (by decide : 2^32 ≤ 2^64)), ?_⟩
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    simp only [Activation.region]
    rcases hApartNum with he | he
    · right
      rw [Nat.add_sub_cancel' (show fr.low.toNat ≤ fr.rsp.toNat from Nat.le_trans (Nat.le_add_right _ 144) hRoom)]
      exact Nat.le_trans (Nat.le_add_right _ 8) (Nat.le_trans he hx)
    · left
      exact Nat.le_trans hx' he
  have hvalueA (m : Ram) (k p : Nat) (hk : k ≤ p) (hp : p < 8)
      (hf : RamWriteFrame m0 m [span (a 0) (2*k)]) :
      memLoad m (a p) 16 = memLoad fr.original (a p) 16 := by
    clear hRet h39 h50 h51 hTypes hWrite hRead hRetRead hStack hStackRead hDest hDestRead hPrev hApart hhelperApart hfs hslot8
    rw [hf.memLoad_eq (a := a p) (k := 16) ⟨by rw [ha' p (Nat.le_of_lt hp)]; omega, ?_⟩]
    · apply hsavedSource <;> rw [ha' p (Nat.le_of_lt hp)] <;> omega
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst r
      simp only [span, ha' 0 (by decide), ha' p (Nat.le_of_lt hp)]
      omega
  have hvalueB (m : Ram) (k p : Nat) (hk : k ≤ 8) (hp : p < 8)
      (hf : RamWriteFrame m0 m [span (a 0) (2*k)]) :
      memLoad m (b p) 16 = memLoad fr.original (b p) 16 := by
    clear hRet h39 h50 h51 hTypes hWrite hRead hRetRead hStack hStackRead hDest hDestRead hPrev hApart hhelperApart hfs hslot8
    rw [hf.memLoad_eq (a := b p) (k := 16) ⟨by rw [hb' p (Nat.le_of_lt hp)]; omega, ?_⟩]
    · apply hsavedSource <;> rw [hb' p (Nat.le_of_lt hp)] <;> omega
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst r
      simp only [span, ha' 0 (by decide), hb' p (Nat.le_of_lt hp)]
      omega
  have hwithin (k : Nat) : RegionsWithin [span (a 0) (2*k)] [span (a 0) (2*(k+1))] := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    refine ⟨span (a 0) (2*(k+1)), by simp, Nat.le_refl _, ?_⟩
    simp only [span]
    omega
  have hframeStep (m : Ram) (k : Nat) (hk : k < 8) (v : BitVec 16)
      (hf : RamWriteFrame m0 m [span (a 0) (2*k)]) :
      RamWriteFrame m0 (memStore m (a k) v) [span (a 0) (2*(k+1))] := by
    apply ((RamWriteFrame.refl m0 [span (a 0) (2*(k+1))]).trans hf (hwithin k)).memStore v
    refine ⟨span (a 0) (2*(k+1)), by simp, ?_⟩
    simp only [InRegion, span, ha' 0 (by decide), ha' k (Nat.le_of_lt hk)]
    omega
  have hword (m : Ram) (k : Nat) (hk : k < 8)
      (hf : RamWriteFrame m0 m [span (a 0) (2*k)]) :
      word m k = xorColumnsWord (memLoad fr.original (b k) 16)
        (memLoad fr.original (a k) 16) fr.r8.toNat := by
    dsimp only [word]
    rw [columnMachineWord_eq _ _ _ hrot, hvalueA m k k (by omega) hk hf,
      hvalueB m k k (by omega) hk hf]
  let ideal (k : Nat) := xorColumnsWord (memLoad fr.original (b k) 16)
    (memLoad fr.original (a k) 16) fr.r8.toNat
  let m1 := memStore m0 (a 0) (ideal 0)
  let m2 := memStore m1 (a 1) (ideal 1)
  let m3 := memStore m2 (a 2) (ideal 2)
  let m4 := memStore m3 (a 3) (ideal 3)
  let m5 := memStore m4 (a 4) (ideal 4)
  let m6 := memStore m5 (a 5) (ideal 5)
  let m7 := memStore m6 (a 6) (ideal 6)
  let m8 := memStore m7 (a 7) (ideal 7)
  have hf0 : RamWriteFrame m0 m0 [span (a 0) 0] := RamWriteFrame.refl _ _
  have hw0 := hword m0 0 (by decide) hf0
  have hf1 : RamWriteFrame m0 m1 [span (a 0) 2] := hframeStep m0 0 (by decide) (ideal 0) hf0
  have hw1 := hword m1 1 (by decide) hf1
  have hf2 : RamWriteFrame m0 m2 [span (a 0) 4] := hframeStep m1 1 (by decide) (ideal 1) hf1
  have hw2 := hword m2 2 (by decide) hf2
  have hf3 : RamWriteFrame m0 m3 [span (a 0) 6] := hframeStep m2 2 (by decide) (ideal 2) hf2
  have hw3 := hword m3 3 (by decide) hf3
  have hf4 : RamWriteFrame m0 m4 [span (a 0) 8] := hframeStep m3 3 (by decide) (ideal 3) hf3
  have hw4 := hword m4 4 (by decide) hf4
  have hf5 : RamWriteFrame m0 m5 [span (a 0) 10] := hframeStep m4 4 (by decide) (ideal 4) hf4
  have hw5 := hword m5 5 (by decide) hf5
  have hf6 : RamWriteFrame m0 m6 [span (a 0) 12] := hframeStep m5 5 (by decide) (ideal 5) hf5
  have hw6 := hword m6 6 (by decide) hf6
  have hf7 : RamWriteFrame m0 m7 [span (a 0) 14] := hframeStep m6 6 (by decide) (ideal 6) hf6
  have hw7 := hword m7 7 (by decide) hf7
  have hf8 : RamWriteFrame m0 m8 [span (a 0) 16] := hframeStep m7 7 (by decide) (ideal 7) hf7
  have hfsAll : RamWriteFrame fr.original m0 [fr.region, span (a 0) 16] := by
    apply (RamWriteFrame.refl fr.original [fr.region, span (a 0) 16]).trans hfs
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hfall : RamWriteFrame fr.original m8 [fr.region, span (a 0) 16] := by
    apply hfsAll.trans hf8
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    exact ⟨span (a 0) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hfall7 : RamWriteFrame fr.original m7 [fr.region, span (a 0) 16] := by
    apply hfsAll.trans hf7
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    exact ⟨span (a 0) 16, by simp, Nat.le_refl _, by simp only [span]; omega⟩
  have hreturn : memLoad m7 fr.rsp 64 = fr.ret := by
    rw [hfall7.memLoad_eq (a := fr.rsp) (k := 64) ⟨Nat.le_trans hRetReadLow (by decide), ?_⟩]
    · exact hRet
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with hr' | hr'
      · subst r
        simp only [Activation.region]
        omega
      · subst r
        simp only [span, ha' 0 (by decide)]
        rcases hApartNum with he | he <;> omega
  have hretWrite (v : BitVec 16) : memLoad (memStore m7 (a 7) v) fr.rsp 64 = fr.ret := by
    rw [memLoad_memStore_of_rangeApart]
    · exact hreturn
    · apply RangeApart.of_toNat
      · rw [ha' 7 (by decide)]; omega
      · omega
      · rw [ha' 7 (by decide)]
        rcases hApartNum with he | he <;> omega
  have hretWriteRaw (v : BitVec 16) :
      memLoad (memStore (memStore m6 (a 6) (ideal 6))
        (fr.rdi + (fr.rdx <<< 1) + 14) v) fr.rsp 64 = fr.ret := hretWrite v
  have hpost : ∀ p : Fin 8, memLoad m8 (a p.val) 16 =
      xorColumnsWord (memLoad fr.original (b p.val) 16)
        (memLoad fr.original (a p.val) 16) fr.r8.toNat := by
    intro p
    have hop (m : Ram) (i j : Nat) (hi : i < 8) (hj : j < 8) (hne : i ≠ j) (v : BitVec 16) :
        memLoad (memStore m (a i) v) (a j) 16 = memLoad m (a j) 16 := by
      apply memLoad_memStore_of_rangeApart
      apply RangeApart.of_toNat
      · rw [ha' i (by omega)]; omega
      · rw [ha' j (by omega)]; omega
      · rw [ha' i (by omega), ha' j (by omega)]; omega
    have hp' : p.val=0 ∨ p.val=1 ∨ p.val=2 ∨ p.val=3 ∨ p.val=4 ∨ p.val=5 ∨ p.val=6 ∨ p.val=7 := by omega
    rcases hp' with he | he | he | he | he | he | he | he
    · rw [he]
      simp only [m8]
      rw [hop m7 7 0 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 0 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [hop m5 5 0 (by decide) (by decide) (by decide)]
      simp only [m5]
      rw [hop m4 4 0 (by decide) (by decide) (by decide)]
      simp only [m4]
      rw [hop m3 3 0 (by decide) (by decide) (by decide)]
      simp only [m3]
      rw [hop m2 2 0 (by decide) (by decide) (by decide)]
      simp only [m2]
      rw [hop m1 1 0 (by decide) (by decide) (by decide)]
      simp only [m1]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 1 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 1 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [hop m5 5 1 (by decide) (by decide) (by decide)]
      simp only [m5]
      rw [hop m4 4 1 (by decide) (by decide) (by decide)]
      simp only [m4]
      rw [hop m3 3 1 (by decide) (by decide) (by decide)]
      simp only [m3]
      rw [hop m2 2 1 (by decide) (by decide) (by decide)]
      simp only [m2]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 2 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 2 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [hop m5 5 2 (by decide) (by decide) (by decide)]
      simp only [m5]
      rw [hop m4 4 2 (by decide) (by decide) (by decide)]
      simp only [m4]
      rw [hop m3 3 2 (by decide) (by decide) (by decide)]
      simp only [m3]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 3 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 3 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [hop m5 5 3 (by decide) (by decide) (by decide)]
      simp only [m5]
      rw [hop m4 4 3 (by decide) (by decide) (by decide)]
      simp only [m4]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 4 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 4 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [hop m5 5 4 (by decide) (by decide) (by decide)]
      simp only [m5]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 5 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [hop m6 6 5 (by decide) (by decide) (by decide)]
      simp only [m6]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [hop m7 7 6 (by decide) (by decide) (by decide)]
      simp only [m7]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    · rw [he]
      simp only [m8]
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
  have hreturnLow : (memLoad (memStore m6 (a 6) (ideal 6)) fr.rsp 64).toNat < 2^32 := by
    change (memLoad m7 fr.rsp 64).toNat < 2^32
    rw [hreturn]
    exact hRetLow
  simp only [m7] at hreturn
  have haNat0 := ha 0 (by decide)
  have hbNat0 := hb 0 (by decide)
  have haNat1 := ha 1 (by decide)
  have hbNat1 := hb 1 (by decide)
  have haNat2 := ha 2 (by decide)
  have hbNat2 := hb 2 (by decide)
  have haNat3 := ha 3 (by decide)
  have hbNat3 := hb 3 (by decide)
  have haNat4 := ha 4 (by decide)
  have hbNat4 := hb 4 (by decide)
  have haNat5 := ha 5 (by decide)
  have hbNat5 := hb 5 (by decide)
  have haNat6 := ha 6 (by decide)
  have hbNat6 := hb 6 (by decide)
  have haNat7 := ha 7 (by decide)
  have hbNat7 := hb 7 (by decide)
  have haNat8 := ha 8 (by decide)
  have hbNat8 := hb 8 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero, BitVec.add_zero] at haNat0 hbNat0 haNat1 hbNat1 haNat2 hbNat2 haNat3 hbNat3 haNat4 hbNat4 haNat5 hbNat5 haNat6 hbNat6 haNat7 hbNat7 haNat8 hbNat8
  have hDest0 := hDest.of_frame hfs
  have hDestRead0 := hDest0.readable
  have hPrev0 := hPrev.of_frame hfs
  have hDest1 := hDest0.of_frame hf1
  have hDestRead1 := hDest1.readable
  have hPrev1 := hPrev0.of_frame hf1
  have hDest2 := hDest0.of_frame hf2
  have hDestRead2 := hDest2.readable
  have hPrev2 := hPrev0.of_frame hf2
  have hDest3 := hDest0.of_frame hf3
  have hDestRead3 := hDest3.readable
  have hPrev3 := hPrev0.of_frame hf3
  have hDest4 := hDest0.of_frame hf4
  have hDestRead4 := hDest4.readable
  have hPrev4 := hPrev0.of_frame hf4
  have hDest5 := hDest0.of_frame hf5
  have hDestRead5 := hDest5.readable
  have hPrev5 := hPrev0.of_frame hf5
  have hDest6 := hDest0.of_frame hf6
  have hDestRead6 := hDest6.readable
  have hPrev6 := hPrev0.of_frame hf6
  have hDest7 := hDest0.of_frame hf7
  have hDestRead7 := hDest7.readable
  have hPrev7 := hPrev0.of_frame hf7
  dsimp only [Activation.original] at *
  runtime_context [hRet, hreturn, hreturnLow, hretWriteRaw, hb0, hp0, haNat0, hbNat0, haNat1, hbNat1, haNat2, hbNat2, haNat3, hbNat3, haNat4, hbNat4, haNat5, hbNat5, haNat6, hbNat6, haNat7, hbNat7, haNat8, hbNat8]
  refine ⟨?output, ?execution, ?tag, ?atoms, ?typed, ?frame, ?words⟩
  case execution =>
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hp0, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104020, _, m0⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hb0, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104029, _, m0⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hp1, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l10408b, _, memStore m0 (a 0) (word m0 0)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw0]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104094, _, m1⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 1, Nat.reduceMul, hp2, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l1040f5, _, memStore m1 (a 1) (word m1 1)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw1]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb2, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l1040fe, _, m2⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 2, Nat.reduceMul, hp3, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l10415f, _, memStore m2 (a 2) (word m2 2)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw2]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb3, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104168, _, m3⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 3, Nat.reduceMul, hp4, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l1041c9, _, memStore m3 (a 3) (word m3 3)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw3]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb4, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l1041d2, _, m4⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 4, Nat.reduceMul, hp5, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104233, _, memStore m4 (a 4) (word m4 4)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw4]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb5, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l10423c, _, m5⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 5, Nat.reduceMul, hp6, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l10429d, _, memStore m5 (a 5) (word m5 5)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw5]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb6, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l1042a6, _, m6⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.next
    · cfg_eval
      simp only [BitVec.ofNat_eq_ofNat, hindexed 6, Nat.reduceMul, hp7, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104303, _, memStore m6 (a 6) (word m6 6)⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      conv => lhs; rw [hw6]
    apply Program.Exec.next
    · cfg_eval
      simp only [hb7, Bool.false_eq_true, ↓reduceIte]
      runtime_guards next
      change Outcome.next (⟨⟨LIR.Label.l104308, _, m7⟩, []⟩ : CFG.State Value Ram LIR.Label signature Reg.count) = _
      rfl
    apply Program.Exec.done
    cfg_eval
    simp only [BitVec.ofNat_eq_ofNat, hindexed 7, Nat.reduceMul]
    runtime_guards returned
    change Outcome.done (⟨_, _, memStore m7 (a 7) (word m7 7)⟩ : Output Value Ram Reg.count) = _
    conv => lhs; rw [hw7]
  case tag => runtime_finish [hretWriteRaw, hreturn]
  case atoms =>
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
    repeat' apply And.intro
    all_goals first | trivial | (runtime_finish [Activation.entryReg, Activation.entryValue]; all_goals first | rfl | exact h39 | exact h50 | exact h51)
  case typed =>
    clear haNat0 hbNat0 haNat1 hbNat1 haNat2 hbNat2 haNat3 hbNat3 haNat4 hbNat4 haNat5 hbNat5 haNat6 hbNat6 haNat7 hbNat7 haNat8 hbNat8
    apply GPRsTyped.of_updates hTypes [0, 1, 4, 6, 9, 10]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r, hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have he : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 8 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    change RamWriteFrame fr.original m8 _
    simpa only [hAddrA 0 (by decide), Nat.add_zero] using hfall
  case words =>
    change ∀ p : Fin 8, memLoad m8 _ 16 = _
    intro p
    simpa only [hAddrA p.val (Nat.le_of_lt p.isLt), hAddrB p.val (Nat.le_of_lt p.isLt)] using hpost p

end AesGcm.Proofs.Machine.AES16.KeySchedule
