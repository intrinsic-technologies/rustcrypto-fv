import X86Proofs.Instructions.Movs.Execution
import Sha1.Proofs.Compress.Machine.Memory
import Sha1.Proofs.Common.Instructions.MemoryWriteFrame

namespace Sha1.Proofs.MemoryRoutines.Movsq

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program

theorem readyMidRep_repMovsq [Bindings] {s : RamState} (h : ReadyMidRep s)
    (htables : ∀ i < 8, ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)) :
    ReadyMidRep (repMovsqAfter s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsqAfter s)).external := by
    rw [clearRep_external, repMovsqAfter_external]
    exact Sha1.Proofs.Common.Instructions.MemoryWriteFrame.identityPageTableMemory_memStore
      (ReadyToStep.memory (s := clearRep s) h).tables _ _ htables
  exact ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovsq s) htab

structure ReadyRepLoop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  dstAlign : (rdi.read s).toNat % 8 = 0
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * count ≤ (rsi.read s).toNat
  dstTables : ∀ i < 8 * count, ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 3

theorem ReadyRepLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem ReadyRepLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : ReadyRepLoop rex s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (repMovsqAfter s)) := by
  have := h.srcLow
  have := h.dstLow
  have := h.dstAlign
  exact rep_movsq_step hstride s h.ready rex hrex h.df h.code h.codeLow
    (hcount := h.rcx_ne hpos) (hsrc := by omega) (hdst := by omega)
    (hsrcMem := fun i hi ↦ h.srcMem i (by omega))
    (hdstMem := fun i hi ↦ h.dstMem i (by omega))

theorem ReadyRepLoop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s (count + 1)) : rcx.read (repMovsqAfter s) = BitVec.ofNat 64 count := by
  rw [repMovsqAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem ReadyRepLoop.source_frame [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s count) (j : Nat) (hj : j < 8 * count) :
    (repMovsqAfter s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsqAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem ReadyRepLoop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s (count + 2)) : ReadyRepLoop rex (repMovsqAfter s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hal := h.dstAlign
  have hrip : (repMovsqAfter s).RIP = s.RIP := by
    rw [repMovsqAfter_rip s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsqAfter s) = rsi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rsi s
  have hd : rdi.read (repMovsqAfter s) = rdi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rdi s
  have hsn : (rsi.read (repMovsqAfter s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsqAfter s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨readyMidRep_repMovsq h.ready (fun i hi ↦ h.dstTables i (by omega)), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsqAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (8 + i) (by omega)]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsqAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat]
    exact h.dstTables (8 + i) (by omega)
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

theorem rep_movsq_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState)
    (h : ReadyRepLoop rex s (count + 1)) :
    RepDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = repMovsqAfter s := nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsqAfter s).Repeat_String_Operation = false := by
      rw [repMovsqAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (readyMidRep_repMovsq h.ready (fun i hi ↦ h.dstTables i (by omega))).ready hflag
    · rw [repMovsqAfter_rip s h.ready.msr, hc]; rfl
    · rw [repMovsqAfter_rcx, hc]
    · exact repMovsqAfter_rsi s
    · exact repMovsqAfter_rdi s
    · intro i hi
      exact repMovsqAfter_copy s i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsq s
  | succ k ih =>
    have hnext : nextState s = repMovsqAfter s := nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsqAfter s) = rsi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rsi s
    have hd : rdi.read (repMovsqAfter s) = rdi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rdi s
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsqAfter s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsqAfter_copy s i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsqAfter s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsqAfter s).RIP = s.RIP := by
      rw [repMovsqAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 8) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsq s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

theorem ReadyRepLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyRepLoop rex s (count + 1))
    (hstart : s.RIP ≠ boundary.rip) (hend : BitVec.add s.RIP 3#64 ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride hrex (by omega)
    have hi : (repMovsqAfter s).RIP ≠ boundary.rip := by
      rw [repMovsqAfter_rip s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride hrex (by omega)
    have hrip : (repMovsqAfter s).RIP = s.RIP := by
      rw [repMovsqAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega)
        (by have := h.srcLow; omega), ↓reduceIte]
    have ha : Advances boundary 1 s (repMovsqAfter s) :=
      Advances.of_step hs (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repMovsqAfter s) h.next (by rw [hrip]; exact hstart)
      (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

structure RepMovsqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstAlign : 0 < (rcx.read s).toNat → (rdi.read s).toNat % 8 = 0
  srcMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : ∀ i < 8 * (rcx.read s).toNat,
    ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3

theorem RepMovsqPre.loop [Bindings] {p : BitVec 64} {rex : UInt8} {s : RamState}
    (hpre : RepMovsqPre p s) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s) (hpos : 0 < (rcx.read s).toNat) :
    ReadyRepLoop rex s (rcx.read s).toNat := by
  refine ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
    hpre.rip ▸ hcode.low (by simp) (by simp), ?_, hpre.srcLow, hpre.dstLow,
    hpre.dstAlign hpos, hpre.srcMem, hpre.dstMem, hpre.disjoint,
    hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rep_movsq_zero_done [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s)
    (hrip : s.RIP = p) (hzero : rcx.read s = 0) :
    RepDone s (nextStates 1 s) 0 := by
  have hs := rep_movsq_step_zero s h.midRep rex hrex (hrip ▸ hcode.bytesAt)
    (hrip ▸ hcode.low (by simp) (by simp)) hzero
  rw [nextStates_one, nextState_of_step hs]
  have hag : AgreesExcept [.rip] s (repMovsqZeroAfter s) :=
    (AgreesExcept.repMovsqZero s).of_clearRep h.ready.repeatClear (repMovsqZeroAfter_repeat s)
  refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
    repMovsqZeroAfter_rip s h.ready.msr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hag.read (by simp), hzero]
  · change rsi.read (repMovsqZeroAfter s) = rsi.read s + 0
    rw [hag.read (by simp)]
    exact (BitVec.add_zero _).symm
  · change rdi.read (repMovsqZeroAfter s) = rdi.read s + 0
    rw [hag.read (by simp)]
    exact (BitVec.add_zero _).symm
  · intro i hi
    omega
  · rw [clearRep_eq h.ready.repeatClear]
    exact hag.mono (by simp)

theorem rep_movsq_zero_advances [Bindings] (boundary : ReturnBoundary)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s)
    (hrip : s.RIP = p) (hzero : rcx.read s = 0) (hend : p + 3#64 ≠ boundary.rip) :
    Advances boundary 1 s (nextStates 1 s) := by
  have hs := rep_movsq_step_zero s h.midRep rex hrex (hrip ▸ hcode.bytesAt)
    (hrip ▸ hcode.low (by simp) (by simp)) hzero
  rw [nextStates_one, nextState_of_step hs]
  apply Advances.of_step hs
  left
  rw [repMovsqZeroAfter_rip s h.ready.msr, hrip]
  exact hend

theorem rep_movsq_done [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s)
    (hpre : RepMovsqPre p s) :
    RepDone s (nextStates (max (rcx.read s).toNat 1) s) (rcx.read s).toNat := by
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    exact rep_movsq_zero_done p rex hrex s h hcode hpre.rip hz
  · have hr := hpre.loop h hcode (by omega)
    rw [hn] at hr
    rw [Nat.max_eq_left (by omega)]
    exact rep_movsq_loop hstride hrex k s hr

theorem rep_movsq_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s)
    (hpre : RepMovsqPre p s) (hstart : p ≠ boundary.rip) (hend : p + 3#64 ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s
      (nextStates (max (rcx.read s).toNat 1) s) := by
  rcases hn : (rcx.read s).toNat with _ | k
  · exact rep_movsq_zero_advances boundary p rex hrex s h hcode hpre.rip
      (BitVec.eq_of_toNat_eq hn) hend
  · have hr := hpre.loop h hcode (by omega)
    rw [hn] at hr
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride hrex boundary k s (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

theorem rep_movsq_agrees [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s)
    (hpre : RepMovsqPre p s) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip]
      s (nextStates (max (rcx.read s).toNat 1) s) := by
  have ha := (rep_movsq_done hstride p rex hrex s h hcode hpre).agrees
  rw [clearRep_eq h.ready.repeatClear] at ha
  exact ha

end Sha1.Proofs.MemoryRoutines.Movsq
