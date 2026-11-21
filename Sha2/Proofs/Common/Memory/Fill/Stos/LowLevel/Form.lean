import Sha2.Proofs.Common.Memory.Fill.StosOperation

namespace Sha2.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem rep_stos_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (bytes : Nat) (hbytes : bytes = 1 ∨ bytes = 8)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : bytes = 8 → ctx.rex_w = 1)
    (hcount : rcx.read t ≠ 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hdst : (rdi.read t).toNat + bytes ≤ 2^32)
    (hdstMem : ∀ i < bytes, (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    ((if bytes = 1 then X86.Instructions.REP_STOSB_0 ip ctx
      else X86.Instructions.REP_STOSQ_0 ip ctx)).run t =
      (.ok (), repCount (stosSpec bytes { t with Next_IP := ip })) := by
  have hop := stos_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) bytes hbytes ctx hes hdf hdst hdstMem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  rcases hbytes with rfl | rfl
  case' inl =>
    simp only [↓reduceIte]
    unfold X86.Instructions.REP_STOSB_0
  case' inr =>
    have hw' := hw rfl
    simp only [show ¬ ((8 : Nat) = 1) from by decide, ↓reduceIte]
    unfold X86.Instructions.REP_STOSQ_0
    simp only [hw', show ((1 : BitVec 1) == 0) = false from rfl]
    simp only [hw'] at hop
  all_goals
    simp only [hrex2, hlock] at hop
    simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
    simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
      show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
    rw [specM_bind_run _ _ (rcx_run _)]
    refine (specM_bind_run _ _ (checkedSliceRead_full_run _ _)).trans ?_
    have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
      simp only [x86_runtime, beq_eq_false_iff_ne]
      intro he
      exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
    rw [hnz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ _ _ (by
      have hn : (rcx.read t).toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hcount
      exact_mod_cast Nat.pos_of_ne_zero hn))]
    simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
      List.forIn_nil, bind_assoc]
    refine (specM_bind_run _ _ hop).trans ?_
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead_full_run _ _)]
    have hsub (a : RamState) (v : BitVec 64) :
        (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
          X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
    rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
    simp only [pure_bind]
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead_full_run _ _)]
    have hzero (a : RamState) (v : BitVec 64) :
        (liftM (Std.Bits.Is_Zero (size := 64) v) :
          X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
    rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
    rfl

theorem rep_stos_form_zero [Bindings] (bytes : Nat) (hbytes : bytes = 1 ∨ bytes = 8)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : bytes = 8 → ctx.rex_w = 1)
    (hcount : rcx.read t = 0) :
    ((if bytes = 1 then X86.Instructions.REP_STOSB_0 ip ctx
      else X86.Instructions.REP_STOSQ_0 ip ctx)).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  rcases hbytes with rfl | rfl
  case' inl =>
    simp only [↓reduceIte]
    unfold X86.Instructions.REP_STOSB_0
  case' inr =>
    have hw' := hw rfl
    simp only [show ¬ ((8 : Nat) = 1) from by decide, ↓reduceIte]
    unfold X86.Instructions.REP_STOSQ_0
    simp only [hw', show ((1 : BitVec 1) == 0) = false from rfl]
  all_goals
    simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
    simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
      show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
    rw [specM_bind_run _ _ (rcx_run _)]
    refine (specM_bind_run _ _ (checkedSliceRead_full_run _ _)).trans ?_
    have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
    rw [hz]
    simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
    rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
      (s := { t with Next_IP := ip }) rfl]
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead_full_run _ _)]
    have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
    rw [hz']
    rfl

end Sha2.Proofs.Common.Memory.Fill.Stos
