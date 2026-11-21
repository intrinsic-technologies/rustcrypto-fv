import Sha3.Proofs.Memory
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.AfterStep
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Store

namespace Sha3.Proofs.Stos

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

abbrev rdi : Operand 64 := .reg 7
abbrev rcx : Operand 64 := .reg 1

theorem rdi_run (u : RamState) :
    (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (rdi.read u), u) := by
  simp only [RDI, Int.zero_le_ofNat, Int.reduceLT, gprGet_eq, Int.reduceToNat, bind_pure_comp,
    ExceptT.run_map,
    Operand.read, BitVec.ofNat_eq_ofNat, Fin.getElem_fin, BitVec.setWidth_eq]
  rfl

theorem writeRDI64_run (u : RamState) (v : BitVec 64) :
    (Write_RDI (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rdi.write u v) := by
  unfold Write_RDI
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rdi_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RDI_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp only [Operand.write_reg64, Int.reduceToNat, gprIndex, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk, Fin.isValue]
  rfl

theorem zeroExtend64_run (x : BitVec 64) (u : RamState) :
    (Std.Bits.Zero_Extend (source_size := 64) x 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
  simp [x86_runtime]

theorem ofInt_div8 (n : Nat) : BitVec.ofInt 64 ((n : Int) / 8) = BitVec.ofNat 64 (n / 8) := by
  rw [show (n : Int) / 8 = ((n / 8 : Nat) : Int) by omega, BitVec.ofInt_natCast]

theorem rcx_run (u : RamState) :
    (RCX : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (rcx.read u), u) := by
  simp only [RCX, Int.zero_le_ofNat, Int.reduceLT, gprGet_eq, Int.reduceToNat, Int.toNat_one,
    bind_pure_comp,
    ExceptT.run_map, Operand.read, BitVec.ofNat_eq_ofNat, Fin.getElem_fin, BitVec.setWidth_eq]
  rfl

theorem writeRCX64_run (u : RamState) (v : BitVec 64) :
    (Write_RCX (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rcx.write u v) := by
  unfold Write_RCX
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rcx_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RCX_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp only [Operand.write_reg64, Int.reduceToNat, gprIndex, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat,
    Nat.reducePow, Nat.one_mod, Fin.mk_one, Fin.isValue, Fin.val_one]
  rfl

theorem rcx_read_write (u : RamState) (v : BitVec 64) : rcx.read (rcx.write u v) = v := by
  simp

theorem getRepeatStringStride_run [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (u : RamState) (size count : Int) (hpos : 0 < count) :
    (Get_Repeat_String_Stride size count : X86.Runtime.SpecM X86.Exception RamState Int).run u =
      (.ok 1, u) := by
  unfold Get_Repeat_String_Stride
  rw [specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
    (.ok u, u) from rfl)]
  apply specM_liftNoSourceException_run
  have := hstride u size count hpos
  erw [this]
  rfl

def DirectionFlagClear (r : BitVec 64) : Prop := r.extractLsb' 10 1 = 0

def repCount (u : RamState) : RamState :=
  { rcx.write u (rcx.read u - 1) with Repeat_String_Operation := !(rcx.read u - 1 == 0#64) }

def stosSpec (n : Nat) (t : RamState) : RamState :=
  rdi.write ((Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
    ((Operand.reg 0 : Operand n).read t)) (rdi.read t + BitVec.ofNat 64 (n / 8))

theorem store_string_operation [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.STORE_STRING 64 n ctx).run t = (.ok (), stosSpec n t) := by
  have hwrite := logicalMemWrite_run_any t h false (rdi.read t) n hn
    ((Operand.reg 0 : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, hdf]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  have hrax (k : Nat) (hk : k ≤ 64) :
      (X86.Runtime.CheckedSlice.read t.GPR[gprIndex 0] 0 k :
        X86.Runtime.SpecM X86.Exception RamState (BitVec k)).run t =
          (.ok ((Operand.reg 0 : Operand k).read t), t) := by
    exact checkedSliceRead_zero_run t t.GPR[gprIndex 0] k (by omega) (by omega)
  unfold X86.Instructions.Operations.STORE_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (rax_run t)]
    refine (specM_bind_run _ _ (hrax _ (by decide))).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [stosSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess, ofInt_div8]

theorem rep_stosq_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hdst : (rdi.read t).toNat + 8 ≤ 2^32)
    (hdstMem : ∀ i, i < 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.REP_STOSQ_0 ip ctx).run t =
      (.ok (), repCount (stosSpec 64 { t with Next_IP := ip })) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (.inr (.inr (.inr rfl))) ctx
    hes hdf hdst hdstMem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_STOSQ_0
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
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ (by
    simp only [X86.Runtime.Unsigned]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp only [Operand.read_reg64, Int.reduceToNat, BitVec.ofNat_eq_ofNat, Fin.getElem_fin,
      BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, ne_eq, Int.natCast_pos, gt_iff_lt] at this ⊢
    omega))]
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

theorem rep_stosq_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1) (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_STOSQ_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_STOSQ_0
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
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_stosb_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hdst : (rdi.read t).toNat + 1 ≤ 2^32)
    (hdstMem : ∀ i, i < 1 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.REP_STOSB_0 ip ctx).run t =
      (.ok (), repCount (stosSpec 8 { t with Next_IP := ip })) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (.inl rfl) ctx
    hes hdf hdst hdstMem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_STOSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ (by
    simp only [X86.Runtime.Unsigned]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp only [Operand.read_reg64, Int.reduceToNat, BitVec.ofNat_eq_ofNat, Fin.getElem_fin,
      BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, ne_eq, Int.natCast_pos, gt_iff_lt] at this ⊢
    omega))]
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

theorem rep_stosb_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_STOSB_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_STOSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem decodeLegacy0_run_of_opcodeAA [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAA, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AA ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0_run_of_opcodeAB [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAB, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AB ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0OpcodeAA_run_of_rep (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 2 := by
  simp only [Select_Legacy_0_Opcode_AA, HAnd.hAnd, AndOp.and, strictAnd, hrep, Int.reduceBEq,
    Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_self]
  rfl

theorem selectLegacy0OpcodeAB_run_of_rep_rexW (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 5 := by
  simp only [Select_Legacy_0_Opcode_AB, HAnd.hAnd, AndOp.and, strictAnd, Bool.true_and, hw,
    BitVec.ofNat_eq_ofNat, Int.toNat_one, BitVec.reduceBEq, Bool.and_false, hrep, Int.reduceBEq,
    Bool.and_self,
    Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_true]
  rfl

theorem decodeLegacy0OpcodeAB_run_of_rep_rexW [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (hw : context.rex_w = 1)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSQ_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_rexW context hrep hw)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_rex_AB [Bindings] (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP [0xF3, rex, 0xAB])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.REP_STOSQ_0 (BitVec.add s.RIP 3#64)
        (repRexContext s.DS rex.toBitVec)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, rex, 0xAB] := hcode
  have f3 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xAB, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have hw : (repRexContext s.DS rex.toBitVec).rex_w = 1 := by
    simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at hrex
    rcases hrex with h | h | h | h | h | h | h | h <;> simp [repRexContext, rexContext, h]
  rw [decodeLegacy0_run_of_opcodeAB _ _ _ _ rfl f3 (hmode 4),
    decodeLegacy0OpcodeAB_run_of_rep_rexW _ _ _ rfl hw (hmode 4) hfeatures,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]

theorem decodeLegacy0OpcodeAA_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (X86.Instructions.REP_STOSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAA_run_of_rep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_AA [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xAA]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.REP_STOSB_0 (BitVec.add s.RIP 2#64)
        (repContext s.DS)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, 0xAA] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xAA, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeAA _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeAA_run_of_rep _ _ _ rfl (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

theorem step_f3_legacy0_midRep [Bindings] (s t : RamState) (h : ReadyMidRep s)
    (op : UInt8) (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP [0xF3, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hrep : scanPreservesRepeat op.toBitVec (repContext s.DS) = true)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep t)) := by
  apply step_of_fetchAndExecute s t h.readyToStepCore _ hmode
  have hf := fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady [0xF3] op
    [] (by simp [scanPrefix_f3]) hop (by simp) hcode hlow
  have hpreserve : scanPreservesRepeat op.toBitVec
      (scanContext (beforeFetch s).DS (PrefixSegments.ofState (beforeFetch s)) [0xf3]) = true := hrep
  rw [hf, hpreserve]
  exact completeDecoded_run_ok _ _ hdecode

def clearRep (s : RamState) : RamState := { s with Repeat_String_Operation := false }

theorem midRep_dataReady [Bindings] {s : RamState} (h : ReadyMidRep s) : DataReady s :=
  (ReadyToStep.dataReady (s := clearRep s) h).of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
    (ReadyToStep.memory (s := clearRep s) h).tables

def repStosAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (stosSpec n {t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len)})

def repStosZeroAfter (len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    {t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false}

theorem repRexContext_rex_w {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (seg : Segment) :
    (repRexContext seg rex.toBitVec).rex_w = 1 := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at hrex
  rcases hrex with h | h | h | h | h | h | h | h <;> simp [repRexContext, rexContext, h]

theorem rep_stosq_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP [0xF3, rex, 0xAB])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hdst : (rdi.read s).toNat + 8 ≤ 2^32)
    (hdstMem : ∀ i, i < 8 → (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repStosAfter 64 3 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_rex_AB s h rex hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := (midRep_dataReady h).of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosq_form hstride t _ _ ht hmode rfl rfl rfl (repRexContext_rex_w hrex _)
    hcpu.es hdf hcount hdst hdstMem] at hdecode
  exact step_f3_rex_legacy0 s _ h rex 0xAB [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stosq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP [0xF3, rex, 0xAB])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repStosZeroAfter 3 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_rex_AB s h rex hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  rw [rep_stosq_form_zero t _ _ rfl rfl rfl (repRexContext_rex_w hrex _) hcount] at hdecode
  exact step_f3_rex_legacy0 s _ h rex 0xAB [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stosb_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP [0xF3, 0xAA])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hdst : (rdi.read s).toNat + 1 ≤ 2^32)
    (hdstMem : ∀ i, i < 1 → (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repStosAfter 8 2 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_AA s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := (midRep_dataReady h).of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosb_form hstride t _ _ ht hmode rfl rfl rfl
    hcpu.es hdf hcount hdst hdstMem] at hdecode
  exact step_f3_legacy0_midRep s _ h 0xAA
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow rfl hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stosb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xAA])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repStosZeroAfter 2 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_AA s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  rw [rep_stosb_form_zero t _ _ rfl rfl rfl hcount] at hdecode
  exact step_f3_legacy0_midRep s _ h 0xAA
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow rfl hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem repStosAfter_external (n len : Nat) (s : RamState) :
    (repStosAfter n len s).external =
      memStore s.external (rdi.read s) ((Operand.reg 0 : Operand n).read s) := rfl

theorem repStosAfter_rflags (n len : Nat) (s : RamState) :
    (repStosAfter n len s).RFLAGS = s.RFLAGS := rfl

theorem repStosAfter_gpr (n len : Nat) (s : RamState) :
    (repStosAfter n len s).GPR =
      Vector.set (Vector.set s.GPR 7 (BitVec.add s.GPR[7] (BitVec.ofNat 64 (n / 8))))
        1 (s.GPR[1] - 1) := by
  simp only [repStosAfter, afterStep, finishStep, repCount, Operand.write, stosSpec, dataAccess,
    afterFetches,
    beforeFetch, resetStepFields, BitVec.ofNat_eq_ofNat, Int.reduceToNat, BitVec.add_eq,
    Operand.read, gprIndex,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk, Fin.getElem_fin,
    Fin.isValue, BitVec.setWidth_eq,
    Nat.zero_mod, Fin.zero_eta, Nat.reduceAdd, Fin.val_zero, mergeGPR_64, Nat.one_mod,
    Fin.mk_one, Fin.val_one,
    Vector.getElem_set, Bool.not_false, Bool.not_not, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  rfl

theorem repStosAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repStosAfter n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp only [Operand.read, Int.reduceToNat, repStosAfter_gpr, BitVec.add_eq,
    BitVec.ofNat_eq_ofNat, gprIndex,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk, Fin.getElem_fin,
    Fin.isValue, Vector.getElem_set,
    BitVec.setWidth_eq]
  rfl

theorem repStosAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repStosAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repStosAfter_gpr, gprIndex]

theorem repStosAfter_rax (n len : Nat) (s : RamState) (m : Nat) :
    (Operand.reg 0 : Operand m).read (repStosAfter n len s) =
      (Operand.reg 0 : Operand m).read s := by
  simp [Operand.read, repStosAfter_gpr, gprIndex]

theorem repStosAfter_rsp (n len : Nat) (s : RamState) :
    (repStosAfter n len s).GPR[4] = s.GPR[4] := by
  simp [repStosAfter_gpr]

theorem rcx_read_stosSpec (n : Nat) (s : RamState) : rcx.read (stosSpec n s) = rcx.read s := by
  simp only [stosSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_reg_write_mem,
    Operand.read_reg_dataAccess]

theorem repStosAfter_repeat (n len : Nat) (s : RamState) :
    (repStosAfter n len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  rfl

theorem repStosAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosAfter n len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  simp [stosSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem agreesExcept_repStos (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (n / 8), .rip] (clearRep s)
      (clearRep (repStosAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repStosAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h7]
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · change (repStosAfter n len s).external[x]? = s.external[x]?
    rw [repStosAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, clearRep, repStosAfter, repCount, afterStep, finishStep, stosSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · change (repStosAfter n len s).external[x]?.isSome = true
    rw [repStosAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem midRep_repStos [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat)
    (htables : IdentityPageTableMemory (repStosAfter n len s).external) :
    ReadyMidRep (repStosAfter n len s) :=
  ReadyToStep.of_agreesExcept h (agreesExcept_repStos n len s) htables

theorem repStosAfter_zero (n len : Nat) (s : RamState) (i : Nat)
    (hi : i < n / 8) (hn : n ≤ 128)
    (hz : (Operand.reg 0 : Operand n).read s = 0) :
    (repStosAfter n len s).external[rdi.read s + BitVec.ofNat 64 i]? = some 0 := by
  rw [repStosAfter_external, hz, memStore_getElem?_self _ _ _ hn i hi]
  simp [storedByte]

theorem repStosZeroAfter_external (len : Nat) (s : RamState) :
    (repStosZeroAfter len s).external = s.external := rfl

theorem repStosZeroAfter_rip (len : Nat) (s : RamState)
    (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosZeroAfter len s).RIP = BitVec.add s.RIP (BitVec.ofNat 64 len) := by
  simp [repStosZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repStosZeroAfter_repeat (len : Nat) (s : RamState) :
    (repStosZeroAfter len s).Repeat_String_Operation = false := rfl

theorem agreesExcept_repStosZero (len : Nat) (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repStosZeroAfter len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, clearRep, repStosZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

inductive Kind where
  | byte
  | quad

def Kind.bits : Kind → Nat
  | .byte => 8
  | .quad => 64

def Kind.bytes (kind : Kind) : Nat := kind.bits / 8

def Kind.code : Kind → List UInt8
  | .byte => [0xF3, 0xAA]
  | .quad => [0xF3, 0x48, 0xAB]

def Kind.after (kind : Kind) (s : RamState) : RamState :=
  repStosAfter kind.bits kind.code.length s

theorem Kind.bytes_pos (kind : Kind) : 0 < kind.bytes := by cases kind <;> decide

theorem Kind.bits_le (kind : Kind) : kind.bits ≤ 128 := by cases kind <;> decide

theorem add_ofNat_add_ofNat (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem toNat_add_ofNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2^64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt h]

theorem ofNat_succ_sub_one (c : Nat) :
    BitVec.ofNat 64 (c + 1) - 1 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem ofNat_ne_zero {c : Nat} (h0 : 0 < c) (h : c < 2^64) : BitVec.ofNat 64 c ≠ 0 := by
  intro he
  have := congrArg BitVec.toNat he
  have h1 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h1] at this
  omega

theorem midRep_msr [Bindings] {s : RamState} (h : ReadyMidRep s) :
    s.«MSRLIST::In_Process» = false := (ReadyToStep.ready (s := clearRep s) h).msr

structure ReadyLoop [Bindings] (kind : Kind) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP kind.code
  codeLow : s.RIP.toNat + kind.code.length ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countBound : count < 2^64
  dstLow : (rdi.read s).toNat + kind.bytes * count ≤ 2^32
  dstMem : ∀ i < kind.bytes * count,
    (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : (Prelude.MemoryRegion.mk (rdi.read s).toNat (kind.bytes * count)).Avoids
    Sha3.Spec.Program.InPageTables
  dstCode : RangeApart (rdi.read s) (kind.bytes * count) s.RIP kind.code.length

theorem ReadyLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {kind : Kind} {s : RamState} {count : Nat} (h : ReadyLoop kind s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (kind.after s)) := by
  have hnz : rcx.read s ≠ 0 := h.counter ▸ ofNat_ne_zero hpos h.countBound
  have hlow := h.dstLow
  cases kind with
  | byte =>
    exact rep_stosb_step hstride s h.ready h.df h.code h.codeLow hnz
      (by simp only [Kind.bytes, Kind.bits, Nat.reduceDiv, Nat.one_mul] at hlow; omega)
      (fun i hi => h.dstMem i (by simpa [Kind.bytes, Kind.bits] using Nat.lt_of_lt_of_le hi hpos))
  | quad =>
    exact rep_stosq_step hstride s h.ready 0x48 (by simp [RexWPrefix]) h.df h.code h.codeLow hnz
      (by simp only [Kind.bytes, Kind.bits] at hlow; omega)
      (fun i hi => h.dstMem i (by simp only [Kind.bytes, Kind.bits]; omega))

theorem ReadyLoop.after_ready [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 1)) : ReadyMidRep (kind.after s) := by
  apply midRep_repStos h.ready
  rw [repStosAfter_external]
  let region : Prelude.MemoryRegion := ⟨(rdi.read s).toNat, kind.bytes * (count + 1)⟩
  apply identityPageTableMemory_memStore_of_avoids s _ _ (#v[region])
    (ReadyToStep.memory (s := clearRep s) h.ready).tables
  · intro i hi
    refine ⟨region, by simp, ?_⟩
    have hlow := h.dstLow
    simp only [Nat.mul_add, Nat.mul_one] at hlow
    change (rdi.read s).toNat ≤ (rdi.read s + BitVec.ofNat 64 i).toNat ∧
      (rdi.read s + BitVec.ofNat 64 i).toNat < (rdi.read s).toNat + kind.bytes * (count + 1)
    change i < kind.bytes at hi
    rw [toNat_add_ofNat _ _ (by omega)]
    simp only [Nat.mul_add, Nat.mul_one]
    constructor <;> omega
  · intro r hr
    have : r = region := by simpa using hr
    subst r
    exact h.dstTables

theorem ReadyLoop.after_rip [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 2)) : (kind.after s).RIP = s.RIP := by
  rw [Kind.after, repStosAfter_rip _ _ _ (midRep_msr h.ready), h.counter]
  have hc : count + 1 < 2^64 := by have := h.countBound; omega
  simp only [show count + 2 = (count + 1) + 1 from rfl, ofNat_succ_sub_one,
    ofNat_ne_zero (by omega) hc, ↓reduceIte]

theorem ReadyLoop.next [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 2)) : ReadyLoop kind (kind.after s) (count + 1) := by
  have hlow := h.dstLow
  simp only [Nat.mul_succ] at hlow
  have hd : rdi.read (kind.after s) = rdi.read s + BitVec.ofNat 64 kind.bytes :=
    repStosAfter_rdi _ _ _
  have hdn : (rdi.read (kind.after s)).toNat = (rdi.read s).toNat + kind.bytes := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hb := kind.bytes_pos
  refine ⟨h.after_ready, h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.after_rip, show (kind.after s).external = _ from repStosAfter_external _ _ _,
      memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by change j < kind.bytes at hj; simp only [Nat.mul_succ]; omega) i hi he
  · rw [h.after_rip]; exact h.codeLow
  · rw [Kind.after, repStosAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countBound; omega
  · rw [hdn]; simp only [Nat.mul_add, Nat.mul_one]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat]
    change (repStosAfter kind.bits kind.code.length s).external[_]?.isSome = true
    rw [repStosAfter_external]
    apply memStore_isSome
    apply h.dstMem
    simp only [Nat.mul_succ] at hi ⊢
    omega
  · intro address hcontains
    apply h.dstTables address
    simp only [Prelude.MemoryRegion.Contains] at hcontains ⊢
    rw [hdn] at hcontains
    simp only [Nat.mul_succ] at hcontains ⊢
    constructor <;> omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, h.after_rip]
    apply h.dstCode (kind.bytes + i) _ j hj
    simp only [Nat.mul_succ] at hi ⊢
    omega

structure Done [Bindings] (kind : Kind) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length)
  counter : rcx.read t = 0
  destination : rdi.read t = rdi.read s + BitVec.ofNat 64 (kind.bytes * count)
  zero : ∀ i < kind.bytes * count, t.external[rdi.read s + BitVec.ofNat 64 i]? = some 0
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (kind.bytes * count), .rip]
    (clearRep s) t

theorem clearRep_eq {s : RamState} (h : s.Repeat_String_Operation = false) : clearRep s = s := by
  have : ∀ b, s.Repeat_String_Operation = b → {s with Repeat_String_Operation := b} = s := by
    rintro b rfl
    rfl
  exact this _ h

theorem rep_stos_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (count : Nat) (s : RamState) (h : ReadyLoop kind s (count + 1))
    (hz : (Operand.reg 0 : Operand kind.bits).read s = 0)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary (count + 1) s t ∧ Done kind s t (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hc : rcx.read s - 1 = 0 := by rw [h.counter]; rfl
    have hflag : (kind.after s).Repeat_String_Operation = false := by
      rw [Kind.after, repStosAfter_repeat, hc]; rfl
    refine ⟨kind.after s, Advances.of_step (h.step hstride (by omega)) (.inr ?_),
      ⟨h.after_ready.ready hflag, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [Kind.after, repStosAfter_rsp] using hsp
    · rw [Kind.after, repStosAfter_rip _ _ _ (midRep_msr h.ready), hc]
      rfl
    · rw [Kind.after, repStosAfter_rcx, hc]
    · simpa only [Nat.zero_add, Nat.mul_one, Kind.after, Kind.bytes] using
        repStosAfter_rdi kind.bits kind.code.length s
    · intro i hi
      exact repStosAfter_zero _ _ _ i
        (by simpa only [Nat.zero_add, Nat.mul_one, Kind.after, Kind.bytes] using hi) kind.bits_le hz
    · rw [← clearRep_eq hflag]
      simpa only [Nat.zero_add, Nat.mul_one, Kind.after, Kind.bytes] using
        agreesExcept_repStos kind.bits kind.code.length s
  | succ k ih =>
    have hfirst : Advances boundary 1 s (kind.after s) :=
      Advances.of_step (h.step hstride (by omega)) (.inr (by
        simpa only [Kind.after, repStosAfter_rsp] using hsp))
    have hz' : (Operand.reg 0 : Operand kind.bits).read (kind.after s) = 0 := by
      rw [Kind.after, repStosAfter_rax, hz]
    have hsp' : (kind.after s).GPR[4] ≠ boundary.rsp := by
      simpa only [Kind.after, repStosAfter_rsp] using hsp
    obtain ⟨t, ht, hd⟩ := ih (kind.after s) h.next hz' hsp'
    have hlow := h.dstLow
    simp only [Nat.mul_succ] at hlow
    have hp : rdi.read (kind.after s) = rdi.read s + BitVec.ofNat 64 kind.bytes :=
      repStosAfter_rdi _ _ _
    refine ⟨t, ?_, ⟨hd.ready, ?_, hd.counter, ?_, ?_, ?_⟩⟩
    · simpa only [Nat.add_comm 1] using hfirst.trans ht
    · rw [hd.rip, h.after_rip]
    · rw [hd.destination, hp, add_ofNat_add_ofNat]
      congr 2
      simp only [Nat.mul_succ]
      omega
    · intro i hi
      by_cases hsmall : i < kind.bytes
      · refine (hd.agrees.byte ?_).trans
          (repStosAfter_zero kind.bits kind.code.length s i hsmall kind.bits_le hz)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hp, add_ofNat_add_ofNat] at he
        have he' := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by
          simp only [Nat.mul_succ] at hj; omega)] at he'
        omega
      · have hz := hd.zero (i - kind.bytes) (by
          simp only [Nat.mul_succ] at hi ⊢; omega)
        rw [hp, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)] at hz
        exact hz
    · refine ((agreesExcept_repStos kind.bits kind.code.length s).trans hd.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (kind.bytes * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          refine ⟨j, ?_, he⟩
          change j < kind.bytes at hj
          simp only [Nat.mul_succ]
          omega
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hp, add_ofNat_add_ofNat] at he
          refine ⟨kind.bytes + j, ?_, he⟩
          simp only [Nat.mul_succ] at hj ⊢
          omega

theorem rep_stos_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (count : Nat) (s : RamState) (h : ReadyLoop kind s count)
    (hz : (Operand.reg 0 : Operand kind.bits).read s = 0)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary (max count 1) s t ∧ Done kind s t count := by
  cases count with
  | succ count =>
    simpa only [Nat.succ_eq_add_one, Nat.max_eq_left (Nat.succ_le_succ (Nat.zero_le count))]
      using rep_stos_loop hstride kind count s h hz boundary hsp
  | zero =>
    have hc : rcx.read s = 0 := h.counter
    have hs : Machine.step s = some (.next (repStosZeroAfter kind.code.length s)) := by
      cases kind with
      | byte => exact rep_stosb_step_zero s h.ready h.code h.codeLow hc
      | quad => exact rep_stosq_step_zero s h.ready 0x48 (by simp [RexWPrefix]) h.code h.codeLow hc
    have hflag := repStosZeroAfter_repeat kind.code.length s
    have hag := agreesExcept_repStosZero kind.code.length s
    rw [clearRep_eq hflag] at hag
    refine ⟨repStosZeroAfter kind.code.length s,
      Advances.of_step hs (.inr hsp), ⟨?_, ?_, hc, ?_, ?_, ?_⟩⟩
    · exact ReadyToStep.of_agreesExcept h.ready hag
        (ReadyToStep.memory (s := clearRep s) h.ready).tables
    · exact repStosZeroAfter_rip _ _ (midRep_msr h.ready)
    · change rdi.read s = BitVec.add (rdi.read s) (BitVec.ofNat 64 (kind.bytes * 0))
      rw [Nat.mul_zero]
      exact (BitVec.add_zero _).symm
    · simp
    · apply hag.widen
      · intro c hc _
        have hc' : c = .rip := by simpa using hc
        simp [hc']
      · intro x c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst c
        exact hcov.elim

theorem Done.rflags [Bindings] {kind : Kind} {s t : RamState} {count : Nat}
    (h : Done kind s t count) : t.RFLAGS = s.RFLAGS :=
  h.agrees.rflags (by simp) (by simp)

theorem Done.rsp [Bindings] {kind : Kind} {s t : RamState} {count : Nat}
    (h : Done kind s t count) : t.GPR[4] = s.GPR[4] :=
  h.agrees.agree (.reg 4) (by simp) rfl

theorem Done.repeat_clear [Bindings] {kind : Kind} {s t : RamState} {count : Nat}
    (h : Done kind s t count) : t.Repeat_String_Operation = false := h.ready.ready.repeatClear

end Sha3.Proofs.Stos
