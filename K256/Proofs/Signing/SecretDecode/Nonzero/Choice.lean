import K256.Proofs.Signing.SecretDecode.State
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR

private theorem nonzeroChoiceCall {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (zero : a[0].get 8 = 0)
    (slot : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage) ⟨.l106f3b, a, m⟩ =
      .call ⟨.l127d50, b, memStore m (sp - 8) (0x106f45 : BitVec 64)⟩
        (Verify.resumeAt .l106f45 0x106f45) ∧
      b[4].get 64 = sp - 8 ∧ b[7] = ⟨64, 0⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [1, 2, 3, 5, 6, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] → b[i] = a[i] := by
  refine ⟨?callee, ?run, ?post⟩
  case run =>
    cfg_eval [rsp]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l106f3b
    · rfl
  case post =>
    refine ⟨rfl, ?_, ?_⟩
    · have low : (a[0].get 64).setWidth 8 = a[0].get 8 :=
        BitVec.setWidth_setWidth_of_le _ (by decide)
      change Value.mk 64 (((mergeGPR 8 _ _).setWidth 8).setWidth 64) = _
      simp only [setWidth_mergeGPR8, low, zero]
      rfl
    · intro ⟨i, hi⟩ mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem choiceNonzero {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106f3b fr a m) (limbs : Limbs fr a)
    (zero : a[0].get 8 = 0) :
    ∃ b n, Verify.Core.Reaches .l106f3b a m .l106f45 b n ∧
      Frame .l106f45 fr b n ∧ Limbs fr b ∧ b[0].get 8 = 0 := by
  have atoms := h.atoms
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.gpr, all_cons,
    all_nil, holds_reg, holds_mem, holds_readable, holds_writable,
    holds_fact] at atoms
  obtain ⟨rsp, df, dst, mxcsr, ftw, fcw, rbx, r12, r13, r14, r15, rbp, retRead,
    retValue, retLow, stack, stackLow, aligned, _⟩ := atoms
  let sp : BitVec 64 := fr.rsp - 120
  have getRsp : a[4].get 64 = sp := by
    exact (congrArg (Value.get 64) rsp).trans (Value.get_mk _ _)
  have natSub (d : Nat) (hd : d ≤ 336) :
      (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
    have bound : d < 2^64 := by omega
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
      (show (BitVec.ofNat 64 d).toNat ≤ fr.rsp.toNat by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]; omega)),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have slotAddr : sp - 8 = fr.rsp - 128 := by dsimp only [sp]; bv_omega
  have workAddr : sp - 8 - 1 = fr.rsp - 129 := by dsimp only [sp]; bv_omega
  have stackBase : (fr.rsp - 336).toNat = fr.rsp.toNat - 336 := natSub 336 (by decide)
  have slotBase : (sp - 8).toNat = fr.rsp.toNat - 128 := by
    rw [slotAddr]
    exact natSub 128 (by decide)
  have workBase : (sp - 8 - 1).toNat = fr.rsp.toNat - 129 := by
    rw [workAddr]
    exact natSub 129 (by decide)
  have slot : Writable Extracted.programImage m (sp - 8) 8 :=
    stack.sub (by rw [stackBase, slotBase]; omega) (by rw [stackBase, slotBase]; omega)
  have work : Writable Extracted.programImage m (sp - 8 - 1) 1 :=
    stack.sub (by rw [stackBase, workBase]; omega) (by rw [stackBase, workBase]; omega)
  obtain ⟨b, call, bsp, arg, kept⟩ := nonzeroChoiceCall getRsp zero slot
  obtain ⟨c, n, run, csp, flag, changed, survive⟩ :=
    Verify.resumeChoice call bsp work slot.readable (by decide)
  have sameReg (i : Fin Reg.count)
      (hi : i.val ∈ [1, 2, 3, 5, 6, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51]) : c[i] = a[i] :=
    (survive i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (kept i hi)
  let scratch : MemoryRegion := ⟨(sp - 8 - 1).toNat, 9⟩
  have pushed : RamWriteFrame m (memStore m (sp - 8) (0x106f45 : BitVec 64)) [scratch] := by
    refine (RamWriteFrame.refl _ _).memStore _ ⟨scratch, List.mem_singleton_self _, ?_⟩
    change (sp - 8 - 1).toNat ≤ (sp - 8).toNat ∧
      (sp - 8).toNat + 8 ≤ (sp - 8 - 1).toNat + 9 ∧ (sp - 8).toNat + 8 ≤ 2^64
    rw [slotBase, workBase]
    omega
  have written : RamWriteFrame m n [scratch] := by
    refine pushed.trans changed ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨scratch, List.mem_singleton_self _, Nat.le_refl _, by dsimp only [scratch]; omega⟩
  have inside : RegionsWithin [scratch] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, List.mem_singleton_self _, ?_, ?_⟩
    all_goals simp only [scratch, Activation.region, low, stackBase, workBase]; omega
  have sameLoad (d : Nat) (hd : d ≤ 120) :
      memLoad n (fr.rsp - BitVec.ofNat 64 d) 64 =
        memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 := by
    refine written.memLoad_eq ⟨?_, ?_⟩
    · rw [natSub d (by omega)]
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change (sp - 8 - 1).toNat + 9 ≤ (fr.rsp - BitVec.ofNat 64 d).toNat
      rw [workBase, natSub d (by omega)]
      omega
  have sameRet : memLoad n fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [BitVec.sub_zero] using sameLoad 0 (by decide)
  refine ⟨c, n, run, ⟨?_, h.writes.trans written inside, ?_⟩, ?_, ?_⟩
  · simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.gpr, all_cons,
      all_nil, holds_reg, holds_mem, holds_readable, holds_writable,
      holds_fact]
    exact ⟨csp, (sameReg 22 (by decide)).trans df, (sameReg 3 (by decide)).trans dst,
      (sameReg 39 (by decide)).trans mxcsr, (sameReg 50 (by decide)).trans ftw,
      (sameReg 51 (by decide)).trans fcw, (sameLoad 48 (by decide)).trans rbx,
      (sameLoad 40 (by decide)).trans r12, (sameLoad 32 (by decide)).trans r13,
      (sameLoad 24 (by decide)).trans r14, (sameLoad 16 (by decide)).trans r15,
      (sameLoad 8 (by decide)).trans rbp, retRead.of_frame written, sameRet.trans retValue,
      retLow, stack.of_frame written, stackLow, aligned, trivial⟩
  · intro i mem
    by_cases isArg : i.val = 7
    · have eq : i = 7 := Fin.ext isArg
      subst i
      exact congrArg Value.width ((survive 7 (by decide)).trans arg)
    · have keep : i.val ∈ [1, 2, 3, 5, 6, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
        omega
      exact (congrArg Value.width (sameReg i keep)).trans (h.widths i mem)
  · exact ⟨(sameReg 14 (by decide)).trans limbs.w0, (sameReg 15 (by decide)).trans limbs.w1,
      (sameReg 12 (by decide)).trans limbs.w2, (sameReg 13 (by decide)).trans limbs.w3,
      (congrArg Value.width (sameReg 5 (by decide))).trans limbs.rbpWidth⟩
  · rw [flag, arg]
    rfl

end K256.Proofs.Signing.SecretDecode
