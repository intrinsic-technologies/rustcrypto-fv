import K256.Proofs.Signing.SecretDecode.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem compareBlock {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (room : 336 ≤ fr.rsp.toNat) (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106e35 fr a m)
    (words : ParseSignature.scalarLimbsAt m (fr.rsp - 80) fr.original fr.rsi)
    (valid : Generate.Sampling.orderFlag (word fr 0) (word fr 1) (word fr 2) (word fr 3) = 1) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l106e35,a,m⟩ =
      .call ⟨.l127d50,b,n⟩ ⟨.l106ee4,#v[],rfl,some ⟨64,0x106ee4⟩⟩ ∧
      b[7] = ⟨64,1⟩ ∧ b[4] = ⟨64,fr.rsp - 128⟩ ∧ Limbs fr b ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,22,39,50,51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b ∧
      RamWriteFrame m n [⟨(fr.rsp - 128).toNat,16⟩] ∧
      memLoad n (fr.rsp - 128) 64 = 0x106ee4 := by
  have atoms := h.atoms
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at atoms
  obtain ⟨rspVal, _, _, rbpVal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 120 := congrArg (Value.get 64) rspVal
  have limb0 : memLoad m (fr.rsp - 80) 64 = word fr 0 := by
    rw [show fr.rsp - 80 = wordAddr (fr.rsp - 80) 64 0 by
      change fr.rsp - 80 = fr.rsp - 80 + 0
      bv_omega]
    exact words 0 (by decide)
  have limb1 : memLoad m (fr.rsp - 72) 64 = word fr 1 := by
    rw [show fr.rsp - 72 = wordAddr (fr.rsp - 80) 64 1 by
      change fr.rsp - 72 = fr.rsp - 80 + 8
      bv_omega]
    exact words 1 (by decide)
  have limb2 : memLoad m (fr.rsp - 64) 64 = word fr 2 := by
    rw [show fr.rsp - 64 = wordAddr (fr.rsp - 80) 64 2 by
      change fr.rsp - 64 = fr.rsp - 80 + 16
      bv_omega]
    exact words 2 (by decide)
  have limb3 : memLoad m (fr.rsp - 56) 64 = word fr 3 := by
    rw [show fr.rsp - 56 = wordAddr (fr.rsp - 80) 64 3 by
      change fr.rsp - 56 = fr.rsp - 80 + 24
      bv_omega]
    exact words 3 (by decide)
  have sameRead (mem : Ram) (addr v : BitVec 64) :
      memLoad (memStore mem addr v) addr 64 = v :=
    memLoad_memStore_same mem addr v (by decide) (by decide)
  have readByte (mem : Ram) (addr v : BitVec 64) :
      memLoad (memStore mem addr v) addr 8 = v.extractLsb' 0 8 :=
    memLoad_memStore_within mem v 8 0 (BitVec.add_zero _).symm (by decide) (by decide) (by decide)
  have borrow : ParseSignature.Scalar.borrowChain (word fr 0) (word fr 1) (word fr 2) (word fr 3) = 1 := by
    rwa [ParseSignature.Scalar.borrowChain_eq, ← Generate.Sampling.limbsValue,
      ← Generate.Sampling.orderFlag_eq]
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, sameRead, readByte, limb0, limb1, limb2, limb3]
    simp only [sameRead, readByte]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l106e35)
    rfl
  case post =>
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · apply congrArg (Value.mk 64)
      let byte := (ParseSignature.Scalar.borrowChain
        (word fr 0) (word fr 1) (word fr 2) (word fr 3)).extractLsb' 0 8
      change ((mergeGPR 8 (byte &&& 1) (byte.setWidth 64)).setWidth 8 |>.setWidth 64) = 1
      rw [show byte = 1 by dsimp only [byte]; rw [borrow]; rfl]
      rfl
    · exact ⟨rfl, rfl, rfl, rfl, congrArg Value.width rbpVal⟩
    · rintro ⟨i, hi⟩ hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ hmem
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact h.widths 8 (by decide) | exact h.widths 9 (by decide)
    · have addr (k : BitVec 64) (hk : k.toNat ≤ 128) :
          (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
      have inScratch (k : BitVec 64) (hk : 120 ≤ k.toNat ∧ k.toNat ≤ 128) :
          InRegions [⟨(fr.rsp - 128).toNat, 16⟩] (fr.rsp - k) 8 := by
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        change (fr.rsp - 128).toNat ≤ (fr.rsp - k).toNat ∧
          (fr.rsp - k).toNat + 8 ≤ (fr.rsp - 128).toNat + 16 ∧ (fr.rsp - k).toNat + 8 ≤ 2^64
        rw [addr 128 (by decide), addr k hk.2]
        simp only [BitVec.reduceToNat]
        omega
      apply RamWriteFrame.memStore _ _ (inScratch 128 (by decide))
      repeat' apply RamWriteFrame.memStore _ _ (inScratch 120 (by decide))
      exact RamWriteFrame.refl _ _
    · exact sameRead _ _ _

end K256.Proofs.Signing.SecretDecode
