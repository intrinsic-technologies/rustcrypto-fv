import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine.Invert.Core.Batch (signedAt_of_copy signedAt_of_frame)

open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

private theorem countWords {n : Nat} (hn : n < 591) :
    let r := (BitVec.ofNat 64 (591 - n)).setWidth 32
    let k := BitVec.ofNat 32 (count n)
    (r = k ↔ n + count n = 591) ∧ (r-k).setWidth 64 = BitVec.ofNat 64 (591 - (n + count n)) := by
  dsimp only
  rw [BitVec.setWidth_ofNat_of_le (by decide)]
  have hk : count n ≤ 591 - n := Nat.min_le_right ..
  have hr : 591 - n < 2^32 := by omega
  have hs : count n < 2^32 := by omega
  constructor
  · rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]
    omega
  · rw [BitVec.ofNat_sub_ofNat_of_le _ _ hs hk, BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega),
      Nat.sub_sub]

private theorem branchRows (P : Prop) [Decidable P] (c : Registers) (q : Ram) :
    (if P then Transfer.jump (Label := Label) (signature := signature) (results := Reg.count) ⟨.l109948, c, q⟩ else .jump ⟨.l1097fe, c, q⟩) =
      .jump ⟨if P then .l109948 else .l1097fe, c, q⟩ := by by_cases h : P <;> simp [h]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
private theorem copyBlock {a : Registers} {m : Ram} {x : Word} {n : Nat} (hn : n < 591)
    (rsp : a[4].get 64 = x - 16)
    (shift : a[5].get 32 = BitVec.ofNat 32 (count n))
    (rem : memLoad m (x + 336) 64 = BitVec.ofNat 64 (591 - n))
    (win : Writable Extracted.programImage m x 360) :
    ∃ c q, Reaches .l109763 a m (if n+count n = 591 then .l109948 else .l1097fe) c q ∧
      c[4] = ⟨64,x⟩ ∧ c[12] = a[12] ∧
      c[6] = ⟨64,BitVec.ofNat 64 (591 - (n+count n))⟩ ∧
      Controls a c ∧ RamWriteFrame m q [⟨(x+96).toNat,80⟩] ∧
      (∀ i < 5, memLoad q (wordAddr (x+96) 64 i) 64 = memLoad m (wordAddr (x+176) 64 i) 64) ∧
      (∀ i < 5, memLoad q (wordAddr (x+136) 64 i) 64 = memLoad m (wordAddr (x+216) 64 i) 64) := by
  have small := win.readable.low
  have shift32 : (a[5].get 64).setWidth 32 = BitVec.ofNat 32 (count n) :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans shift
  obtain ⟨last, leftover⟩ := countWords hn
  have label : (if (BitVec.ofNat 64 (591-n)).setWidth 32 = BitVec.ofNat 32 (count n)
      then Label.l109948 else .l1097fe) = (if n + count n = 591 then .l109948 else .l1097fe) :=
    ite_congr (propext last) (fun _ => rfl) (fun _ => rfl)
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    refine .step ?_ (.refl _)
    change (program.runBlock _ _).next _ _ = _
    cfg_eval [b_l109763, b_l109763_1, rsp, shift, show x - 16 + 16 = x by bv_omega]
    segment_words [rem]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l109763)
    rw [shift32, branchRows, label]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
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

theorem copyRows {a b c : Registers} {m p q : Ram} {sp : Word}
    {s n : Nat} {d e : Int} {w : Words} (h : Entry a m sp s)
    (state : LoopState a m sp s n b p d e) (more : n < 591)
    {d' e' : Int} (rows : ModularRows b p sp s n w c q d' e')
    (delta : w.delta.toInt = (Inverse.model s (n+count n)).delta)
    (db : d'.natAbs < domain.n) (eb : e'.natAbs < domain.n)
    (di : (d' * s) % domain.n = (Inverse.model s (n + count n)).f % domain.n)
    (ei : (e' * s) % domain.n = (Inverse.model s (n + count n)).g % domain.n) :
    ∃ c' q', Reaches .l109763 c q (if n+count n = 591 then .l109948 else .l1097fe) c' q' ∧
      LoopState a m sp s (n+count n) c' q' d' e' := by
  have lo := h.depthBound
  have hi := h.high
  have win := (h.stack.of_frame state.frame).of_frame rows.frame
  have shift : c[5].get 32 = BitVec.ofNat 32 (count n) := by
    rw [rows.shift]
    change (BitVec.ofNat 64 (count n)).setWidth 32 = BitVec.ofNat 32 (count n)
    exact BitVec.setWidth_ofNat_of_le (by decide) _
  obtain ⟨last, mem, reach, rsp, deltaReg, remaining, controls, writes, first, second⟩ :=
    copyBlock more (congrArg (Value.get 64) rows.rsp)
      shift rows.remaining (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  let rs := modularWrites sp ++ [⟨(base sp + 96).toNat, 80⟩]
  have total : RamWriteFrame p mem rs := by
    refine ((RamWriteFrame.refl p rs).trans rows.frame ?_).trans writes ?_
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩
  have stable (off : Word) (lb : 256 ≤ off.toNat) (ub : off.toNat + 8 ≤ 304) :
      memLoad mem (base sp + off) 64 =
        memLoad p (base sp + off) 64 := by
    apply total.memLoad_eq
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  refine ⟨last, mem, reach, rsp, ?_, remaining,
    fun i hi => ((controls i hi).trans (rows.controls i hi)).trans (state.kept i hi),
    ?_, state.frame.trans total ?_, ?_, ?_, signedAt_of_copy rows.dValue first,
    signedAt_of_copy rows.eValue second, db, eb, di, ei, ?_, ?_, ?_, ?_⟩
  · rw [deltaReg, rows.delta, ← delta, BitVec.ofInt_toInt]
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
  · rw [stable 280 (by decide) (by decide), stable 264 (by decide) (by decide),
      stable 256 (by decide) (by decide), stable 272 (by decide) (by decide)]
    exact state.originalNonzero
  · exact (stable 288 (by decide) (by decide)).trans state.outputPtr
  · apply (total.memLoad_eq ?_).trans state.modulusPtr
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  · exact (stable 296 (by decide) (by decide)).trans state.modulusInverse

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
