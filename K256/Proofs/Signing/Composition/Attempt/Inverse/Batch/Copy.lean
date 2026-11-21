import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Copy

namespace K256.Proofs.Signing.Composition.Attempt.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore batchLabel CalleeFrame)
open Generate.Generator.Affine.Invert.Core.Batch (count Inner Rows Controls setupWrites linearWrites modularWrites)
open Verify.Core (Registers)
open Standards.SECG.DomainParameters.Secp256k1
open SafeGcd.Batch (Words)

open Generate.LIR
open Generate.Generator.Affine.Invert.Core.Batch (signedAt_of_copy signedAt_of_frame)

open_order_batch Update.Copy (copyBlock)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Nat}

theorem copyRows (h : Entry a m sp z) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram} {s : Words}
    {d' e' : Int} (rows : ModularRows b p sp z j s c q d' e')
    (delta : s.delta.toInt = (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).delta)
    (db : d'.natAbs < domain.n) (eb : e'.natAbs < domain.n)
    (di : (d' * z) % domain.n = (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).f % domain.n)
    (ei : (e' * z) % domain.n = (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).g % domain.n) :
    ∃ c' q', Reaches .l10914e c q (batchLabel (j+1)) c' q' ∧
      LoopState a m sp z (roundsBefore (j+1)) c' q' d' e' := by
  have lo := h.depthBound
  have hi := h.high
  have win := (h.stack.of_frame state.frame).of_frame rows.frame
  have shift : c[15].get 32 = BitVec.ofNat 32 (count j) := by
    rw [rows.shift]
    change (BitVec.ofNat 64 (count j)).setWidth 32 = BitVec.ofNat 32 (count j)
    exact BitVec.setWidth_ofNat_of_le (by decide) _
  obtain ⟨last, mem, reach, rsp, rbp, r14, remaining, controls, writes, first, second⟩ :=
    copyBlock hj (congrArg (Value.get 64) rows.rsp) (congrArg (Value.get 64) rows.second)
      shift rows.remaining (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  let rs := modularWrites sp ++ [⟨(base sp + 208).toNat, 80⟩]
  have total : RamWriteFrame p mem rs := by
    refine ((RamWriteFrame.refl p rs).trans rows.frame ?_).trans writes ?_
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩
  have stable (off : Word) (lb : 288 ≤ off.toNat) (ub : off.toNat + 8 ≤ 336) :
      memLoad mem (base sp + off) 64 =
        memLoad p (base sp + off) 64 := by
    apply total.memLoad_eq
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  refine ⟨last, mem, reach, rsp, ?_, remaining, r14.trans rows.scratch,
    fun i hi => ((controls i hi).trans (rows.controls i hi)).trans (state.kept i hi),
    ?_, state.frame.trans total ?_, ?_, ?_, signedAt_of_copy rows.firstResult first,
    signedAt_of_copy rows.secondResult second, db, eb, di, ei, ?_, ?_, ?_, ?_⟩
  · rw [rbp, rows.delta, ← delta, BitVec.ofInt_toInt]
  · intro i off hm
    apply (total.memLoad_eq ?_).trans (state.saved _ _ hm)
    have bound : 8 ≤ off ∧ off ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      omega
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  · intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [rs, modularWrites, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp only [base] <;> constructor <;> bv_omega
  · apply signedAt_of_frame rows.fValue writes
    simp only [Outside, List.mem_singleton, forall_eq, base]
    bv_omega
  · apply signedAt_of_frame rows.gValue writes
    simp only [Outside, List.mem_singleton, forall_eq, base]
    bv_omega
  · rw [stable 312 (by decide) (by decide), stable 296 (by decide) (by decide),
      stable 288 (by decide) (by decide), stable 304 (by decide) (by decide)]
    exact state.originalNonzero
  · exact (stable 320 (by decide) (by decide)).trans state.outputPtr
  · apply (total.memLoad_eq ?_).trans state.modulusPtr
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  · exact (stable 328 (by decide) (by decide)).trans state.modulusInverse


end K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
