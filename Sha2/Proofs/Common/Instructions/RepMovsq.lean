import Sha2.Proofs.Common.Instructions.CrossPageStore.Memory
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.RepMovsq

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_string_operation [Bindings] (t : RamState) (h : DataReady t) (hmode : In64BitMode t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : (rsi.read t).toNat + n / 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < n / 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 64 n ctx).run t = (.ok (), movsSpec n t) := by
  have hread := logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl)
    hsrc hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := Sha2.Proofs.Common.Instructions.CrossPageStore.logicalMemWrite_run_any (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (dfBit u.RFLAGS), u) = _
    rw [hu, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrsi (u : RamState) : (do
      let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
    (specM_bind_run _ _ (rsi_run u)).trans (hslice _ u)
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrsi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hds, hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrsi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [movsSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt_div8]

theorem rep_movsq_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : (rsi.read t).toNat + 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), repCount (movsSpec 64 { t with Next_IP := ip })) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (.inr (.inr (.inr rfl))) ctx hseg hm64 hds hes hdf hsrc hdst
    hsrcMem hdstMem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  simp only [hlock, hrex2, hw] at hop
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ (by
    simp only [X86.Runtime.Unsigned]; have := BitVec.toNat_ne_iff_ne.mpr hcount; simp at this ⊢; omega))]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsq_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP [0xF3, rex, 0xA5])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : (rsi.read s).toNat + 8 ≤ 2^32) (hdst : (rdi.read s).toNat + 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < 8 → (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < 8 → (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repMovsqAfter s)) := by
  have hdecode := decodeLegacy0_run_of_F3_rex_A5 s h rex hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_form hstride t _ _ ht hmode rfl rfl rfl (repRexContext_rex_w hrex _) rfl rfl
    hcpu.ds hcpu.es hdf hcount hsrc hdst hsrcMem hdstMem] at hdecode
  have hstep := step_f3_rex_legacy0 s _ h rex 0xA5 [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)
  rw [show scanPreservesRepeat (0xA5 : UInt8).toBitVec (repRexContext s.DS rex.toBitVec)
    = true from rfl] at hstep
  exact hstep

structure ReadyRepLoop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
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
  exact rep_movsq_step hstride s h.ready rex hrex h.df h.code h.codeLow (h.rcx_ne hpos) (by omega)
    (by omega) (fun i hi => h.srcMem i (by omega)) (fun i hi => h.dstMem i (by omega))

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
  have hrip : (repMovsqAfter s).RIP = s.RIP := by
    rw [repMovsqAfter_rip s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsqAfter s) = rsi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rsi s
  have hd : rdi.read (repMovsqAfter s) = rdi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rdi s
  have hsn : (rsi.read (repMovsqAfter s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsqAfter s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsq (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsqAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (8 + i) (by omega)]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsqAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

theorem rep_movsq_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : ReadyRepLoop rex s (count + 1)) :
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
    · exact (h.ready.repMovsq (by omega) (by have := h.dstTables; omega)).ready hflag
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
      ·
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
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

structure RepMovsqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3

theorem rep_movsq_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s) (hpre : RepMovsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA5]) t ∧ (repMovsqEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | k
  ·
    have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repMovsqZeroAfter s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repMovsqZeroAfter s) :=
      (AgreesExcept.repMovsqZero s).of_clearRep hrep (repMovsqZeroAfter_repeat s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  ·
    have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_loop hstride hrex k s hready
    have ht : t = nextStates (k + 1) s := by
      simp only [t, hn, show max (k + 1) 1 = k + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsqEffect_components, hn]
      exact hag.mono (by simp)

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

theorem rep_movsq_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) (hstart : p ≠ boundary.rip) (hend : p + 3#64 ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  have hcodeS : BytesAt s s.RIP [0xf3, rex, 0xa5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    apply Advances.of_step hs
    left
    rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]
    exact hend
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride hrex boundary k s (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

theorem rep_movsq_copy [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) :
    ∀ i < 8 * (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rcases hn : (rcx.read s).toNat with _ | k
  · intro i hi; omega
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
        hpre.rip ▸ hcode.low (by simp) (by simp), hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact (rep_movsq_loop hstride hrex k s hr).copy

end Sha2.Proofs.Common.Instructions.RepMovsq
