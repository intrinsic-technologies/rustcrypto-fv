import K256.Proofs.Ecdh.Decode.Convert.Resume
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Sec1.Tactic.Core

namespace K256.Proofs.Ecdh.Decode.Convert
open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Refine K256.Proofs.Lift Ecdh.LIR
private def continuation : StackFrame Value Label signature Reg.count :=
  ⟨.l10fa68,#v[],rfl,some ⟨64,0x10fa68⟩⟩

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem convertEntry (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn10fa10.frameAt .l10fa10 fr))
    (src : Readable fr.original fr.rsi 84)
    (sep : Outside [ParseSignature.callStack fr] fr.rsi 84) :
    ∃ b m, program.runBlock (dialect Extracted.programImage) ⟨.l10fa10,a,fr.original⟩ =
      .call ⟨.l127d50,b,m⟩ continuation ∧ b[7].get 8 = inputFlag fr ∧
      b[4] = ⟨64,fr.rsp - 96⟩ ∧ b[3] = ⟨64,fr.rdi⟩ ∧ coordinates fr b m ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b ∧ RamWriteFrame fr.original m [fr.region] ∧
      memLoad m (fr.rsp - 96) 64 = 0x10fa68 ∧
      ∀ k r : Nat, (k,r) ∈ [(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)] →
        memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
  simp only [Fn10fa10.frameAt, Fn10fa10.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨h4, _, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15, _, _, _,
    retRead, _, _, window, room, _⟩ := entry
  have rsp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) h4
  have rbx : a[3].get 64 = fr.rbx := congrArg (Value.get 64) h3
  have rbp : a[5].get 64 = fr.rbp := congrArg (Value.get 64) h5
  have rsi : a[6].get 64 = fr.rsi := congrArg (Value.get 64) h6
  have rdi : a[7].get 64 = fr.rdi := congrArg (Value.get 64) h7
  have r12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) h12
  have r13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) h13
  have r14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) h14
  have r15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) h15
  have apart := sep.2 _ (List.mem_singleton_self _)
  change fr.rsi.toNat + 84 ≤ fr.low.toNat ∨
    fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat at apart
  have stackFrame {m : Ram} (frame : RamWriteFrame fr.original m [fr.region])
      (k : Nat) (lo : 8 ≤ k) (hi : k ≤ 97) (v : BitVec 64) :
      RamWriteFrame fr.original (memStore m (fr.rsp - BitVec.ofNat 64 k) v) [fr.region] := by
    refine frame.memStore v ⟨fr.region, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ (fr.rsp - BitVec.ofNat 64 k).toNat ∧
      (fr.rsp - BitVec.ofNat 64 k).toNat + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _
    have kn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, kn]; omega), kn]
    have top := retRead.low
    omega
  have loadWord {m : Ram} (frame : RamWriteFrame fr.original m [fr.region])
      (k w : Nat) (bound : k + w / 8 ≤ 84) :
      memLoad m (fr.rsi + BitVec.ofNat 64 k) w =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 k) w := by
    apply frame.memLoad_eq
    have low := src.low
    have addr : (fr.rsi + BitVec.ofNat 64 k).toNat = fr.rsi.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [addr]; omega, ?_⟩
    intro reg hreg
    obtain rfl := List.mem_singleton.mp hreg
    change _ + w / 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    rw [addr]
    omega
  have guard {m : Ram} (frame : RamWriteFrame fr.original m [fr.region])
      (k off len : Nat) (depth : (BitVec.ofNat 64 97 - BitVec.ofNat 64 k).toNat + 8 ≤ 97)
      (fits : off + len ≤ bytes_l10fa10.length) :
      StoreOk Extracted.programImage m (fr.rsp - BitVec.ofNat 64 k) 8
        (0x10fa10 + BitVec.ofNat 64 off) len := by
    apply ParseSignature.storeOk_of_codeRange
      ((window.of_frame frame).of_offsets (addr_sub fr.rsp _) (addr_sub fr.rsp _) ?_)
      (fun x hx => Common.fnCode_subset_programImage x (code_l10fa10 x hx)) fits
    change (0 - BitVec.ofNat 64 k - (0 - BitVec.ofNat 64 97)).toNat + 8 ≤ 97
    rw [show (0 - BitVec.ofNat 64 k) - (0 - BitVec.ofNat 64 97) =
      BitVec.ofNat 64 97 - BitVec.ofNat 64 k by bv_omega]
    exact depth
  have loadGuard {m : Ram} (frame : RamWriteFrame fr.original m [fr.region])
      (k n : Nat) (fits : k + n ≤ 84) : LoadOk m (fr.rsi + BitVec.ofNat 64 k) n := by
    apply LoadOk.of_offsets (src.of_frame frame) rfl (addr_self _)
    have kn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    change (BitVec.ofNat 64 k - 0).toNat + n ≤ 84
    rw [show BitVec.ofNat 64 k - 0 = BitVec.ofNat 64 k by bv_omega, kn]
    exact fits
  have f0 := RamWriteFrame.refl fr.original [fr.region]
  let m1 := memStore fr.original (fr.rsp - 8) fr.rbp
  have s1 : memStore fr.original (fr.rsp - 8) fr.rbp = m1 := rfl
  have g1 : StoreOk Extracted.programImage fr.original (fr.rsp - 8) 8 0x10fa10 1 :=
    guard f0 8 0 1 (by decide) (by decide)
  have f1 : RamWriteFrame fr.original m1 [fr.region] :=
    stackFrame f0 8 (by decide) (by decide) fr.rbp
  let m2 := memStore m1 (fr.rsp - 16) fr.r15
  have s2 : memStore m1 (fr.rsp - 16) fr.r15 = m2 := rfl
  have g2 : StoreOk Extracted.programImage m1 (fr.rsp - 16) 8 0x10fa11 2 :=
    guard f1 16 1 2 (by decide) (by decide)
  have f2 : RamWriteFrame fr.original m2 [fr.region] :=
    stackFrame f1 16 (by decide) (by decide) fr.r15
  let m3 := memStore m2 (fr.rsp - 24) fr.r14
  have s3 : memStore m2 (fr.rsp - 24) fr.r14 = m3 := rfl
  have g3 : StoreOk Extracted.programImage m2 (fr.rsp - 24) 8 0x10fa13 2 :=
    guard f2 24 3 2 (by decide) (by decide)
  have f3 : RamWriteFrame fr.original m3 [fr.region] :=
    stackFrame f2 24 (by decide) (by decide) fr.r14
  let m4 := memStore m3 (fr.rsp - 32) fr.r13
  have s4 : memStore m3 (fr.rsp - 32) fr.r13 = m4 := rfl
  have g4 : StoreOk Extracted.programImage m3 (fr.rsp - 32) 8 0x10fa15 2 :=
    guard f3 32 5 2 (by decide) (by decide)
  have f4 : RamWriteFrame fr.original m4 [fr.region] :=
    stackFrame f3 32 (by decide) (by decide) fr.r13
  let m5 := memStore m4 (fr.rsp - 40) fr.r12
  have s5 : memStore m4 (fr.rsp - 40) fr.r12 = m5 := rfl
  have g5 : StoreOk Extracted.programImage m4 (fr.rsp - 40) 8 0x10fa17 2 :=
    guard f4 40 7 2 (by decide) (by decide)
  have f5 : RamWriteFrame fr.original m5 [fr.region] :=
    stackFrame f4 40 (by decide) (by decide) fr.r12
  let m6 := memStore m5 (fr.rsp - 48) fr.rbx
  have s6 : memStore m5 (fr.rsp - 48) fr.rbx = m6 := rfl
  have g6 : StoreOk Extracted.programImage m5 (fr.rsp - 48) 8 0x10fa19 1 :=
    guard f5 48 9 1 (by decide) (by decide)
  have f6 : RamWriteFrame fr.original m6 [fr.region] :=
    stackFrame f5 48 (by decide) (by decide) fr.rbx
  have l5 : LoadOk m6 (fr.rsi + 40) 8 :=
    loadGuard f6 40 8 (by decide)
  have w5 : memLoad m6 (fr.rsi + 40) 64 = inputWord fr 5 :=
    loadWord f6 40 64 (by decide)
  let m7 := memStore m6 (fr.rsp - 88) (inputWord fr 5)
  have s7 : memStore m6 (fr.rsp - 88) (inputWord fr 5) = m7 := rfl
  have g7 : StoreOk Extracted.programImage m6 (fr.rsp - 88) 8 0x10fa25 4 :=
    guard f6 88 21 4 (by decide) (by decide)
  have f7 : RamWriteFrame fr.original m7 [fr.region] :=
    stackFrame f6 88 (by decide) (by decide) (inputWord fr 5)
  have l6 : LoadOk m7 (fr.rsi + 48) 8 :=
    loadGuard f7 48 8 (by decide)
  have w6 : memLoad m7 (fr.rsi + 48) 64 = inputWord fr 6 :=
    loadWord f7 48 64 (by decide)
  let m8 := memStore m7 (fr.rsp - 80) (inputWord fr 6)
  have s8 : memStore m7 (fr.rsp - 80) (inputWord fr 6) = m8 := rfl
  have g8 : StoreOk Extracted.programImage m7 (fr.rsp - 80) 8 0x10fa2d 5 :=
    guard f7 80 29 5 (by decide) (by decide)
  have f8 : RamWriteFrame fr.original m8 [fr.region] :=
    stackFrame f7 80 (by decide) (by decide) (inputWord fr 6)
  have l7 : LoadOk m8 (fr.rsi + 56) 8 :=
    loadGuard f8 56 8 (by decide)
  have w7 : memLoad m8 (fr.rsi + 56) 64 = inputWord fr 7 :=
    loadWord f8 56 64 (by decide)
  let m9 := memStore m8 (fr.rsp - 72) (inputWord fr 7)
  have s9 : memStore m8 (fr.rsp - 72) (inputWord fr 7) = m9 := rfl
  have g9 : StoreOk Extracted.programImage m8 (fr.rsp - 72) 8 0x10fa36 5 :=
    guard f8 72 38 5 (by decide) (by decide)
  have f9 : RamWriteFrame fr.original m9 [fr.region] :=
    stackFrame f8 72 (by decide) (by decide) (inputWord fr 7)
  have l8 : LoadOk m9 (fr.rsi + 64) 8 :=
    loadGuard f9 64 8 (by decide)
  have w8 : memLoad m9 (fr.rsi + 64) 64 = inputWord fr 8 :=
    loadWord f9 64 64 (by decide)
  let m10 := memStore m9 (fr.rsp - 64) (inputWord fr 8)
  have s10 : memStore m9 (fr.rsp - 64) (inputWord fr 8) = m10 := rfl
  have g10 : StoreOk Extracted.programImage m9 (fr.rsp - 64) 8 0x10fa3f 5 :=
    guard f9 64 47 5 (by decide) (by decide)
  have f10 : RamWriteFrame fr.original m10 [fr.region] :=
    stackFrame f9 64 (by decide) (by decide) (inputWord fr 8)
  have l9 : LoadOk m10 (fr.rsi + 72) 8 :=
    loadGuard f10 72 8 (by decide)
  have w9 : memLoad m10 (fr.rsi + 72) 64 = inputWord fr 9 :=
    loadWord f10 72 64 (by decide)
  let m11 := memStore m10 (fr.rsp - 56) (inputWord fr 9)
  have s11 : memStore m10 (fr.rsp - 56) (inputWord fr 9) = m11 := rfl
  have g11 : StoreOk Extracted.programImage m10 (fr.rsp - 56) 8 0x10fa48 5 :=
    guard f10 56 56 5 (by decide) (by decide)
  have f11 : RamWriteFrame fr.original m11 [fr.region] :=
    stackFrame f10 56 (by decide) (by decide) (inputWord fr 9)
  let m12 := memStore m11 (fr.rsp - 96) (0x10fa68 : BitVec 64)
  have s12 : memStore m11 (fr.rsp - 96) (0x10fa68 : BitVec 64) = m12 := rfl
  have g12 : StoreOk Extracted.programImage m11 (fr.rsp - 96) 8 0x10fa63 5 :=
    guard f11 96 83 5 (by decide) (by decide)
  have f12 : RamWriteFrame fr.original m12 [fr.region] :=
    stackFrame f11 96 (by decide) (by decide) (0x10fa68 : BitVec 64)
  have l0 : LoadOk m11 fr.rsi 8 := by
    simpa only [BitVec.add_zero] using loadGuard f11 0 8 (by decide)
  have w0 : memLoad m11 fr.rsi 64 = inputWord fr 0 := by
    simpa only [inputWord, wordAddr, Nat.mul_zero, BitVec.add_zero] using loadWord f11 0 64 (by decide)
  have l1 : LoadOk m11 (fr.rsi + 8) 8 :=
    loadGuard f11 8 8 (by decide)
  have w1 : memLoad m11 (fr.rsi + 8) 64 = inputWord fr 1 :=
    loadWord f11 8 64 (by decide)
  have l2 : LoadOk m11 (fr.rsi + 16) 8 :=
    loadGuard f11 16 8 (by decide)
  have w2 : memLoad m11 (fr.rsi + 16) 64 = inputWord fr 2 :=
    loadWord f11 16 64 (by decide)
  have l3 : LoadOk m11 (fr.rsi + 24) 8 :=
    loadGuard f11 24 8 (by decide)
  have w3 : memLoad m11 (fr.rsi + 24) 64 = inputWord fr 3 :=
    loadWord f11 24 64 (by decide)
  have l4 : LoadOk m11 (fr.rsi + 32) 8 :=
    loadGuard f11 32 8 (by decide)
  have w4 : memLoad m11 (fr.rsi + 32) 64 = inputWord fr 4 :=
    loadWord f11 32 64 (by decide)
  have flagLoad : LoadOk m11 (fr.rsi + 80) 4 := loadGuard f11 80 4 (by decide)
  have flagWord : memLoad m11 (fr.rsi + 80) 32 = memLoad fr.original (fr.rsi + 80) 32 :=
    loadWord f11 80 32 (by decide)
  refine ⟨?_, m12, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, rbx, rbp, rsi, rdi, r12, r13, r14, r15,
      s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12,
      w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, flagWord]
    simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, flagLoad, ↓reduceIte]
    rfl
  case post =>
    refine ⟨?_, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_, ?_, f12, ?_, ?_⟩
    · change ((memLoad fr.original (fr.rsi + 80) 32).setWidth 64).setWidth 8 = inputFlag fr
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
      rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32), extractLsb'_memLoad _ _ 0 8 (by decide) (by decide) (by decide)]
      simp only [inputFlag, Nat.zero_div, BitVec.add_zero]
    · intro i hi
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases h with rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [wordAddr, Nat.reduceDiv, Nat.mul_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]
      case' inr.inl => rw [show fr.rsp - 88 + 8#64 = fr.rsp - 80 by bv_omega]
      case' inr.inr.inl => rw [show fr.rsp - 88 + 16#64 = fr.rsp - 72 by bv_omega]
      case' inr.inr.inr.inl => rw [show fr.rsp - 88 + 24#64 = fr.rsp - 64 by bv_omega]
      case' inr.inr.inr.inr => rw [show fr.rsp - 88 + 32#64 = fr.rsp - 56 by bv_omega]
      all_goals
        simp (disch := store_disch) only [m12, m11, m10, m9, m8, m7,
          memLoad_memStore_same, memLoad_memStore_of_rangeApart]
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact congrArg Value.width h6 | exact congrArg Value.width h2 |
          exact congrArg Value.width h1 | exact congrArg Value.width h8 | exact congrArg Value.width h9
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro k r h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals
        simp (disch := store_disch) only [m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1,
          memLoad_memStore_same, memLoad_memStore_of_rangeApart, BitVec.ofNat_eq_ofNat,
          Activation.entryReg]

end K256.Proofs.Ecdh.Decode.Convert
