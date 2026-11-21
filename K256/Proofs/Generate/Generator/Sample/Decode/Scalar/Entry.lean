import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.LIR.Fn109e60.Frame
import K256.Proofs.Generate.Sampling.Predicate
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxHeartbeats 1400000 in
theorem scalarEntry (fr : Activation) (a : Vector Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn109e60.frameAt .l109e60 fr))
    (src : Readable fr.original fr.rsi 32)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 32) :
    let w := Common.scalarWord fr.original fr.rsi
    ∃ b m, program.runBlock (dialect Extracted.programImage) ⟨.l109e60, a, fr.original⟩ =
      .call ⟨.l127d50, b, m⟩ (callFrame .l109f32 0x109f32) ∧
      b[7] = ⟨64, Sampling.orderFlag (w 0) (w 1) (w 2) (w 3)⟩ ∧
      b[4] = ⟨64, fr.rsp - 64⟩ ∧ b[3] = ⟨64, fr.rdi⟩ ∧
      b[13] = ⟨64, w 0⟩ ∧ b[12] = ⟨64, w 1⟩ ∧ b[15] = ⟨64, w 2⟩ ∧ b[14] = ⟨64, w 3⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5, 22, 39, 50, 51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b ∧ RamWriteFrame fr.original m [fr.region] ∧
      memLoad m (fr.rsp - 64) 64 = 0x109f32 ∧
      ∀ k r, (k, r) ∈ [(40,3), (32,12), (24,13), (16,14), (8,15)] →
        memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
  generalize memory : fr.original = mem at entry src ⊢
  intro w
  simp only [Fn109e60.frameAt, Fn109e60.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨h4, _, _, _, h3, _, h6, h7, h8, h9, h12, h13, h14, h15, _, _, _, retRead,
    _, _, writable, room, _, _⟩ := entry
  have apart := srcApart.2 _ (List.mem_singleton_self _)
  change fr.rsi.toNat + 32 ≤ fr.low.toNat ∨
    fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat at apart
  have rsp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) h4
  have rbx : a[3].get 64 = fr.rbx := congrArg (Value.get 64) h3
  have rsi : a[6].get 64 = fr.rsi := congrArg (Value.get 64) h6
  have rdi : a[7].get 64 = fr.rdi := congrArg (Value.get 64) h7
  have r12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) h12
  have r13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) h13
  have r14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) h14
  have r15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) h15

  have readByte (m : Ram) (b : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m b v) b 8 = v.extractLsb' 0 8 :=
    memLoad_memStore_within m v 8 0 (BitVec.add_zero _).symm (by decide) (by decide) (by decide)
  let saved := memStore (memStore (memStore (memStore (memStore mem (fr.rsp - 8)
    fr.r15) (fr.rsp - 16) fr.r14) (fr.rsp - 24) fr.r13) (fr.rsp - 32) fr.r12)
    (fr.rsp - 40) fr.rbx
  have sameRead (m : Ram) (b v : BitVec 64) : memLoad (memStore m b v) b 64 = v :=
    memLoad_memStore_same m b v (by decide) (by decide)
  have stackAddr (k : Nat) (hk : k ≤ 65) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have h : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h]; omega), h]
  have inStack (k : Nat) (lo : 8 ≤ k) (hi : k ≤ 65) :
      InRegions [fr.region] (fr.rsp - BitVec.ofNat 64 k) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ _ ∧ _ + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _
    rw [stackAddr k hi]
    have top := retRead.low
    omega
  have savedFrame : RamWriteFrame mem saved [fr.region] := by
    dsimp only [saved]
    repeat' apply RamWriteFrame.memStore _ _ (inStack _ (by decide) (by decide))
    exact RamWriteFrame.refl _ _
  have savedLoad (k : Nat) (hk : k + 8 ≤ 32) :
      memLoad saved (fr.rsi + BitVec.ofNat 64 k) 64 =
        memLoad mem (fr.rsi + BitVec.ofNat 64 k) 64 := by
    apply savedFrame.memLoad_eq
    have low := src.low
    have addr : (fr.rsi + BitVec.ofNat 64 k).toNat = fr.rsi.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    change _ + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    rw [addr]
    omega
  have limb0 : bswapSpec (memLoad saved (fr.rsi + 24) 64) = w 0 := by
    simpa only [w, Common.scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using congrArg bswapSpec (savedLoad 24 (by decide))
  have limb1 : bswapSpec (memLoad saved (fr.rsi + 16) 64) = w 1 := by
    simpa only [w, Common.scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using congrArg bswapSpec (savedLoad 16 (by decide))
  have limb2 : bswapSpec (memLoad saved (fr.rsi + 8) 64) = w 2 := by
    simpa only [w, Common.scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using congrArg bswapSpec (savedLoad 8 (by decide))
  have limb3 : bswapSpec (memLoad saved fr.rsi 64) = w 3 := by
    simpa only [w, Common.scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using congrArg bswapSpec (savedLoad 0 (by decide))
  dsimp only [saved] at limb0 limb1 limb2 limb3
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, rbx, rsi, rdi, r12, r13, r14, r15, readByte, sameRead, limb0, limb1, limb2, limb3]
    simp -failIfUnchanged only [limb0, limb1, limb2, limb3, sameRead, readByte]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l109e60)
    rfl
  case post =>
    have flagForm (v : BitVec 64) (bit : v = 0 ∨ v = 1) :
        ((mergeGPR 8 (v.extractLsb' 0 8 &&& 1) ((v.extractLsb' 0 8).setWidth 64)).setWidth 8
            |>.setWidth 64) = v := by
      rcases bit with rfl | rfl <;> rfl
    have flagBit : Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 0 ∨
        Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 := by
      rw [Sampling.orderFlag_eq]
      split <;> simp only [true_or, or_true, eq_self]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · apply congrArg (Value.mk 64)
      exact flagForm _ flagBit
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact congrArg Value.width h8 | exact congrArg Value.width h9
    · repeat' apply RamWriteFrame.memStore _ _ (inStack _ (by decide) (by decide))
      exact RamWriteFrame.refl _ _
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro off reg h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart,
          BitVec.ofNat_eq_ofNat, Activation.entryReg]

end K256.Proofs.Generate.Generator.Sample
