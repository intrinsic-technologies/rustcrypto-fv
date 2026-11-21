import K256.Proofs.Verify.Core.Lincomb.Body

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem lincombPath (e : Entry fr a p digest r s) {b m u v} (hu : u < domain.n)
    (hv : v < domain.n) (h : Products fr b m u v r) :
    ∃ c n, Reaches .l105256 b m .l10526c c n ∧ PointResult fr c n
      (Curve.add domain (Curve.scalarMul domain u domain.G) (Curve.scalarMul domain v p)) r := by
  obtain ⟨c, call, args⟩ := Lincomb.call e h
  obtain ⟨out, run, tag, sp, keep, wf, point⟩ := Lincomb.execute e h args hu hv
  refine ⟨out.values, out.store, .step (b := ⟨⟨.l10fb20, c, Lincomb.push m fr⟩, [Lincomb.resume]⟩) ?_ ?_, ?_⟩
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run Lincomb.resume [] (by rw [tag]; rfl)
  obtain ⟨within, outside⟩ := Lincomb.frameBounds e
  have restore (k : Nat) (hk : 8 ≤ k ∧ k ≤ 40) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply wf.memLoad_eq
    have addr : fr.rsp - BitVec.ofNat 64 k = localSp fr + BitVec.ofNat 64 (488-k) := by
      have sum := congrArg (BitVec.ofNat 64) (show 488 - k + k = 488 by omega)
      rw [BitVec.ofNat_add] at sum
      unfold localSp
      bv_omega
    rw [addr]
    apply outside <;> omega
  have regs (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,15,22,39,50,51]) : out.values[i] = b[i] := by
    apply (keep i ?_).trans (args.keep i ?_)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢ <;> omega
  have valid (i : Fin 4) : (Naf.digits (combinationScalars u v i)).length ≤ 129 := by
    apply Naf.digits_length
    match i with
    | 0 => exact (Generate.Curve.split_correct u hu).2.1
    | 1 => exact (Generate.Curve.split_correct u hu).2.2
    | 2 => exact (Generate.Curve.split_correct v hv).2.1
    | 3 => exact (Generate.Curve.split_correct v hv).2.2
  rw [wnafAccumulator_correct p u v 129 e.onCurve hu hv valid] at point
  exact ⟨⟨⟨sp, (regs 3 (by decide)).trans h.dst, (regs 5 (by decide)).trans h.rbp,
    (regs 22 (by decide)).trans h.df, (regs 39 (by decide)).trans h.mxcsr,
    (regs 50 (by decide)).trans h.ftw, (regs 51 (by decide)).trans h.fcw,
    (restore 40 (by decide)).trans h.rbx, (restore 32 (by decide)).trans h.r12,
    (restore 24 (by decide)).trans h.r13, (restore 16 (by decide)).trans h.r14,
    (restore 8 (by decide)).trans h.r15⟩, h.frame.trans wf within⟩,
    congrArg Value.width ((regs 12 (by decide)).trans h.uPtr),
    congrArg Value.width ((regs 15 (by decide)).trans h.vPtr),
    (keep 13 (by decide)).trans args.result, point,
    h.rAt.of_frame wf (by decide) (outside 256 32 (by decide) (by decide))⟩

end K256.Proofs.Verify.Core
