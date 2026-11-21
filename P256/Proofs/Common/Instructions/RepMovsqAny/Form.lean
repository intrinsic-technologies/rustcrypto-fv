import P256.Proofs.Common.Instructions.CrossPageStore.Memory
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.RepMovsqAny

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
  have hwrite := P256.Proofs.Common.Instructions.CrossPageStore.logicalMemWrite_run_any (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = 0 from hdf]
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
  exact step_f3_rex_legacy0 s _ h rex 0xA5 [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)


end P256.Proofs.Common.Instructions.RepMovsqAny
