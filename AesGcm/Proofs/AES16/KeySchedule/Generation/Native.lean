import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Copy
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Sub
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Xor
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Transform
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Control
import AesGcm.Proofs.AES16.KeySchedule.Generation.Words

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Native

set_option maxHeartbeats 800000 in
theorem step_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes)
    (round : Nat) (hr : (variant use256).Nk / 4 ≤ round)
    (hrLast : round ≤ (variant use256).Nr)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hready : Ready use256 round sp args)
    (hmemory : MemoryReady use256 code mem sp)
    (hkeys : RawSchedulePrefix (variant use256) key round (base use256 sp) mem) :
    ∃ (nextArgs : Values Value Reg.count) (nextMem : Ram),
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨label use256 round, args, mem⟩, []⟩
        ⟨⟨label use256 (round + 1), nextArgs, nextMem⟩, []⟩ ∧
      Ready use256 (round + 1) sp nextArgs ∧ SameFP args nextArgs ∧
      RamWriteFrame mem nextMem (roundRegions use256 sp round) ∧
      (∀ p : Fin 8,
        memLoad nextMem (base use256 sp + BitVec.ofNat 64 (16 * round + 2 * p.val)) 16 =
          Fixslice16.encodeStandard (Machine.KeySchedule.roundKeyBlock (variant use256) key
            ⟨round, by omega⟩) p) := by
  have hr1 : 1 ≤ round := by cases use256 <;> simp only [variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte] at hr <;> omega
  have hn : 1 ≤ (variant use256).Nk / 4 := by cases use256 <;> decide
  let prev := Machine.KeySchedule.roundKeyBlock (variant use256) key ⟨round - 1, by omega⟩
  let back := Machine.KeySchedule.roundKeyBlock (variant use256) key
    ⟨round - (variant use256).Nk / 4, by omega⟩
  obtain ⟨ca, cm, hc, hcr, hcfp, hcf, hcw⟩ :=
    Native.copy_reaches use256 code hcode round hr hrLast args mem sp hready hmemory
  have hcm := memoryReady_of_frame hmemory hcf (round_stack_within hmemory round hrLast)
  have hcopyWords : WordsAt cm (base use256 sp + BitVec.ofNat 64 (16 * round))
      16 (Vector.ofFn (Fixslice16.encodeStandard prev)) := by
    intro p hp
    have h := (hcw ⟨p, hp⟩).trans (hkeys ⟨round - 1, by omega⟩ (by change round - 1 < round; omega) ⟨p, hp⟩)
    simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_comm,
      BitVec.ofNat_add, BitVec.add_assoc] using h
  obtain ⟨sa, sm, hs, hsr, hsfp, hsf, hsw⟩ :=
    Native.sub_reaches use256 code hcode round hrLast ca cm sp hcr hcm _ hcopyWords
  have hsm := memoryReady_of_frame hcm hsf (round_stack_within hcm round hrLast)
  obtain ⟨ta, tm, ht, htsp, htdi, htsi, htdx, ht15, htcx, ht8, htkeep, httypes, htf, htw⟩ :=
    transform_reaches use256 code hcode round hr hrLast sa sm sp hsr hsm _ hsw
  have htm := memoryReady_of_frame hsm htf (round_stack_within hsm round hrLast)
  have hcst : RamWriteFrame mem tm (roundRegions use256 sp round) :=
    (hcf.trans hsf (by intro r hin; exact ⟨r, hin, Nat.le_refl _, Nat.le_refl _⟩)).trans htf
      (by intro r hin; exact ⟨r, hin, Nat.le_refl _, Nat.le_refl _⟩)
  have hprefix := prefix_of_frame hmemory key round hrLast hkeys hcst
  have hback : WordsAt tm
      (base use256 sp + BitVec.ofNat 64 (16 * (round - (variant use256).Nk / 4)))
      16 (Vector.ofFn (Fixslice16.encodeStandard back)) := by
    intro p hp
    have h := hprefix ⟨round - (variant use256).Nk / 4, by omega⟩ (by change round - (variant use256).Nk / 4 < round; omega) ⟨p, hp⟩
    simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_comm,
      BitVec.ofNat_add, BitVec.add_assoc] using h
  have ht39 : ta[39] = sa[39] := htkeep 39 (by decide)
  have h39 : ta[39] = ⟨32, ta[39].get 32⟩ := by rw [ht39]; exact hsr.h39
  have ht50 : ta[50] = sa[50] := htkeep 50 (by decide)
  have h50 : ta[50] = ⟨16, ta[50].get 16⟩ := by rw [ht50]; exact hsr.h50
  have ht51 : ta[51] = sa[51] := htkeep 51 (by decide)
  have h51 : ta[51] = ⟨16, ta[51].get 16⟩ := by rw [ht51]; exact hsr.h51
  have hDF : ta[22] = ⟨1, 0⟩ := (htkeep 22 (by decide)).trans hsr.hDF
  obtain ⟨out, he, htag, hsp, hkeep, htypes, hframe, hwords⟩ :=
    Native.xor_exec use256 code hcode round hr hrLast ta tm sp htm htsp htdi htsi htdx htcx ht8
      httypes h39 h50 h51 hDF _ _ hback htw
  have hkeepSa : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] →
      out.values[r] = sa[r] := by
    intro r hin
    apply (hkeep r ?_).trans (htkeep r hin)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin ⊢
    omega
  have ho15 : out.values[15] = ta[15] := hkeep 15 (by decide)
  obtain ⟨na, ha, hnr, hnfp⟩ := advance_reaches use256 code round hr hrLast sa out.values out.store
    sp hsr hkeepSa (by rw [hsp]; rfl) (by rw [ho15, ht15]; rfl) htypes
  have hlabel : afterLabel use256 (oddRound round) = controlLabel use256 round := by
    cases use256 with
    | false => rfl
    | true =>
      by_cases he : round % 2 = 0
      · have ho : oddRound round = false := by simp [oddRound, he]
        simp only [ho, afterLabel, controlLabel, he, ↓reduceIte]
      · have ho : oddRound round = true := by simp [oddRound, he]
        simp only [ho, afterLabel, controlLabel, he, ↓reduceIte]
  have hresume := CFGCall.exec_reaches_resume he
    (callFrame (afterLabel use256 (oddRound round)) (afterReturn use256 (oddRound round))) []
    (by rw [htag]; change decide (_ = _) = true; simp only [decide_true])
  have hresume' : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨.l104010, ta, memStore tm (sp - 8) (afterReturn use256 (oddRound round))⟩,
        [callFrame (afterLabel use256 (oddRound round)) (afterReturn use256 (oddRound round))]⟩
      ⟨⟨controlLabel use256 round, out.values, out.store⟩, []⟩ := by
    have heq : (callFrame (afterLabel use256 (oddRound round))
        (afterReturn use256 (oddRound round))).resume out =
        ⟨controlLabel use256 round, out.values, out.store⟩ := by
      have hv := CFGCall.resume_arguments
        (callFrame (afterLabel use256 (oddRound round)) (afterReturn use256 (oddRound round))) out
      have hl : ((callFrame (afterLabel use256 (oddRound round))
        (afterReturn use256 (oddRound round))).resume out).label = controlLabel use256 round := hlabel
      have hm : ((callFrame (afterLabel use256 (oddRound round))
        (afterReturn use256 (oddRound round))).resume out).store = out.store := rfl
      generalize (callFrame (afterLabel use256 (oddRound round))
        (afterReturn use256 (oddRound round))).resume out = loc at hv hl hm ⊢
      cases loc with
      | mk lab vals store =>
        dsimp only at hv hl hm
        cases hl; cases hv; cases hm
        rfl
    rw [heq] at hresume
    exact hresume
  have htotal := hc.trans (hs.trans (ht.trans (hresume'.trans ha)))
  have htotalFrame : RamWriteFrame mem out.store (roundRegions use256 sp round) :=
    hcst.trans hframe (by intro r hin; exact ⟨r, hin, Nat.le_refl _, Nat.le_refl _⟩)
  refine ⟨na, out.store, htotal, hnr,
    ⟨hnfp.1.trans (hsfp.1.trans hcfp.1),
      hnfp.2.1.trans (hsfp.2.1.trans hcfp.2.1),
      hnfp.2.2.trans (hsfp.2.2.trans hcfp.2.2)⟩, htotalFrame, ?_⟩
  have hrot : (if use256 && oddRound round then 3 else 7) =
      (if Nat.mod (4 * round) (variant use256).Nk = 0 then 7 else 3) := by
    cases use256 with
    | false =>
      change (7 : Nat) = if (4 * round) % 4 = 0 then 7 else 3
      split <;> omega
    | true =>
      change (if decide (round % 2 ≠ 0) then (3 : Nat) else 7) =
        (if (4 * round) % 8 = 0 then 7 else 3)
      simp only [decide_eq_true_eq]
      split <;> split <;> omega
  have hstart : (variant use256).Nk ≤ 4 * round := by
    cases use256 with
    | false => change 4 ≤ 4 * round; change 1 ≤ round at hr; omega
    | true => change 8 ≤ 4 * round; change 2 ≤ round at hr; omega
  have halgebra := xorColumns_roundKeyBlock (variant use256) key ⟨round, by omega⟩
    (by cases use256 <;> decide) (by change (variant use256).Nk ≤ 4 * round; exact hstart)
  have htransform : substitutedRound use256 round (Fixslice16.subBytes (Fixslice16.encodeStandard prev)) =
      (fun p ↦ Fixslice16.encodeStandard (Standards.NIST.AES.subBytes prev) p ^^^
        (if (if Nat.mod (4 * round) (variant use256).Nk = 0 then
          (rcon (4 * round / (variant use256).Nk))[0] else 0).toBitVec.getLsbD p.val
          then (0x80 : BitVec 16) else 0)) := by
    unfold substitutedRound
    rw [subBytesNots_subBytes_encodeStandard]
    rfl
  have hfinal : xorColumns (Fixslice16.encodeStandard back)
      (substitutedRound use256 round (Fixslice16.subBytes (Fixslice16.encodeStandard prev)))
      (if use256 && oddRound round then 3 else 7) =
      Fixslice16.encodeStandard (Machine.KeySchedule.roundKeyBlock (variant use256) key
        ⟨round, by omega⟩) := by
    rw [htransform, hrot]
    exact halgebra
  rw [hfinal] at hwords
  intro p
  have hw := hwords p.val p.isLt
  simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_comm,
    BitVec.ofNat_add, BitVec.add_assoc] using hw

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
