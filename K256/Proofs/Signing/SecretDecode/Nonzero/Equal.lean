import K256.Proofs.Signing.SecretDecode.State
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Verify.Choice

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem equalNonzero {fr : Activation} {a b : Verify.Core.Registers} {before m : Ram}
    (call : program.runBlock (dialect Extracted.programImage) ⟨.l106eed, a, before⟩ =
      .call ⟨.l127f50, b, m⟩ (Verify.resumeAt .l106f3b 0x106f3b))
    (frame : Frame .l106eed fr a m) (limbs : Limbs fr a)
    (sp : b[4] = ⟨64, fr.rsp - 128⟩) (di : b[7] = ⟨64, fr.rsp - 80⟩)
    (dx : b[2] = ⟨64, fr.rsp - 120⟩) (si : b[6] = ⟨64, 4⟩) (cx : b[1] = ⟨64, 4⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i])
    (ret : memLoad m (fr.rsp - 128) 64 = 0x106f3b)
    (room : 336 ≤ fr.rsp.toNat)
    (different : ¬ ∀ i < 4, memLoad m (wordAddr (fr.rsp - 80) 64 i) 64 =
      memLoad m (wordAddr (fr.rsp - 120) 64 i) 64) :
    ∃ c, Verify.Core.Reaches .l106eed a before .l106f3b c m ∧ Frame .l106f3b fr c m ∧
      Limbs fr c ∧ c[0].get 8 = 0 := by
  have atoms := frame.atoms
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, bx, mx, ft, fc, savedBx, saved12, saved13, saved14, saved15, savedBp,
    slot, tag, retLow, stack, low, aligned, _⟩ := atoms
  let child := {fr with
    original := m, rsp := fr.rsp - 128, low := fr.rsp - 128,
    ret := 0x106f3b, rdi := fr.rsp - 80, rdx := fr.rsp - 120, rsi := 4, rcx := 4,
    rbx := fr.rdi, rbp := a[5].get 64, r8 := a[8].get 64, r9 := a[9].get 64,
    r12 := word fr 2, r13 := word fr 3, r14 := word fr 0, r15 := word fr 1}
  have reg64 (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
    cases v with
    | mk w v => cases h; rfl
  have readable (off : BitVec 64) (n : Nat) (h₁ : n ≤ off.toNat) (h₂ : off.toNat ≤ 336) :
      Readable m (fr.rsp - off) n := by
    apply stack.readable.sub <;> bv_omega
  have cEntry : Atom.All Extracted.programImage b m (Proofs.LIR.Fn127f50.frameAt .l127f50 child) := by
    refine ⟨sp, (keep 22 (by decide)).trans df, cx, dx, (keep 3 (by decide)).trans bx,
      (keep 5 (by decide)).trans (reg64 _ limbs.rbpWidth), si, di,
      (keep 8 (by decide)).trans (reg64 _ (frame.widths 8 (by decide))),
      (keep 9 (by decide)).trans (reg64 _ (frame.widths 9 (by decide))),
      (keep 12 (by decide)).trans limbs.w2, (keep 13 (by decide)).trans limbs.w3,
      (keep 14 (by decide)).trans limbs.w0, (keep 15 (by decide)).trans limbs.w1,
      (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
      (keep 51 (by decide)).trans fc, readable 128 8 (by decide) (by decide), ret,
      by change (0x106f3b : BitVec 64).toNat < 2^32; decide, Nat.le_refl _, ?_, trivial⟩
    change (fr.rsp - 128).toNat % 16 = 8
    rw [BitVec.toNat_sub_of_le (show (128 : BitVec 64) ≤ fr.rsp from BitVec.le_def.mpr (by change 128 ≤ _; omega))]
    change (fr.rsp.toNat - 128) % 16 = 8
    omega
  obtain ⟨out, run, outTag, done_, _, widths, same, iffEq, binary⟩ :=
    Generate.Generator.Sample.ctEq_call Common.fnCode_subset_programImage child rfl rfl
      (readable 80 32 (by decide) (by decide)) (readable 120 32 (by decide) (by decide)) b cEntry
  have reached := Verify.reachesOfCall call (Verify.Transfer.compareExec rfl run) outTag
  change out.store = m at same
  rw [same] at reached
  rw [← Proofs.LIR.Fn127f50.doneAt_canonical] at done_
  simp only [Proofs.LIR.Fn127f50.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨outSp, outDf, outBx, outBp, w2, w3, w0, w1, outMx, outFt, outFc, _⟩ := done_
  refine ⟨out.values, reached, ⟨?_, frame.writes, widths⟩,
    ⟨w0, w1, w2, w3, congrArg Value.width outBp⟩, binary.resolve_right (fun one => different (iffEq.mp one))⟩
  refine ⟨?_, outDf, outBx, outMx, outFt, outFc, savedBx, saved12, saved13, saved14,
    saved15, savedBp, slot, tag, retLow, stack, low, aligned, trivial⟩
  exact outSp.trans (congrArg (Value.mk 64) (show fr.rsp - 128 + 8 = fr.rsp - 120 by bv_omega))

end K256.Proofs.Signing.SecretDecode
