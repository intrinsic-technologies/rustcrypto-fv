import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.State
import K256.Proofs.Generate.LIR.Fn108e30

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

private theorem countWords {j : Nat} (hj : j < 10) :
    let r := (BitVec.ofNat 64 (591 - roundsBefore j)).setWidth 32
    let k := BitVec.ofNat 32 (count j)
    (r = k ↔ j+1 = 10) ∧ (r-k).setWidth 64 = BitVec.ofNat 64 (591 - roundsBefore (j+1)) := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem branchRows (P : Prop) [Decidable P] (c : Registers) (q : Ram) :
    (if P then Transfer.jump (Label := Label) (signature := signature) (results := Reg.count) ⟨.l1093fe, c, q⟩ else .jump ⟨.l1091e4, c, q⟩) =
      .jump ⟨if P then .l1093fe else .l1091e4, c, q⟩ := by by_cases h : P <;> simp [h]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
private theorem copyBlock {a : Registers} {m : Ram} {x : Word} {j : Nat} (hj : j < 10)
    (rsp : a[4].get 64 = x - 16) (second : a[12].get 64 = x + 56)
    (shift : a[15].get 32 = BitVec.ofNat 32 (count j))
    (rem : memLoad m (x + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j))
    (win : Writable Extracted.programImage m x 360) :
    ∃ c q, Reaches .l10914e a m (batchLabel (j+1)) c q ∧
      c[4] = ⟨64,x⟩ ∧ c[5] = a[5] ∧ c[14] = a[14] ∧
      c[2] = ⟨64,BitVec.ofNat 64 (591 - roundsBefore (j+1))⟩ ∧
      Controls a c ∧ RamWriteFrame m q [⟨(x+208).toNat,80⟩] ∧
      (∀ i < 5, memLoad q (wordAddr (x+208) 64 i) 64 = memLoad m (wordAddr (x+16) 64 i) 64) ∧
      (∀ i < 5, memLoad q (wordAddr (x+248) 64 i) 64 = memLoad m (wordAddr (x+56) 64 i) 64) := by
  have small := win.readable.low
  have shift32 : (a[15].get 64).setWidth 32 = BitVec.ofNat 32 (count j) :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans shift
  obtain ⟨last, leftover⟩ := countWords hj
  have label : (if (BitVec.ofNat 64 (591 - roundsBefore j)).setWidth 32 = BitVec.ofNat 32 (count j)
      then Label.l1093fe else .l1091e4) = batchLabel (j+1) := by
    by_cases h : j+1 = 10
    · simp [last.mpr h, batchLabel, h]
    · rw [ite_eq_right (fun e => h (last.mp e)), batchLabel, ite_eq_right h]
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    refine .step ?_ (.refl _)
    change (program.runBlock _ _).next _ _ = _
    generate_block [rsp, second, shift, show x - 16 + 16 = x by bv_omega]
    segment_words [rem]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10914e)
    rw [shift32, branchRows, label]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (Value.mk 64) leftover
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl
    · repeat' apply RamWriteFrame.memStore
      all_goals first | exact RamWriteFrame.refl _ _
                      | exact ⟨_, List.mem_singleton_self _, by unfold InRegion; exact ⟨by bv_omega, by bv_omega, by bv_omega⟩⟩
    all_goals
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl <;>
        simp only [wordAddr, Nat.reduceMul, Nat.reduceDiv, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset] <;>
        segment_words [] <;> rfl

open SafeGcd.Batch (Words)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

theorem copyRows (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram} {s : Words}
    {d' e' : Int} (rows : ModularRows b p sp z j s c q d' e')
    (delta : s.delta.toInt = (Core.model z (roundsBefore (j+1))).delta)
    (db : d'.natAbs < modulus) (eb : e'.natAbs < modulus)
    (di : (d' * z.val) % modulus = (Core.model z (roundsBefore (j+1))).f % modulus)
    (ei : (e' * z.val) % modulus = (Core.model z (roundsBefore (j+1))).g % modulus) :
    ∃ c' q', Reaches .l10914e c q (batchLabel (j+1)) c' q' ∧
      LoopState a m sp z (roundsBefore (j+1)) c' q' d' e' := by
  have lo := h.low
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

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
