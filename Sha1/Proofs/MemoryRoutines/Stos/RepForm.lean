import Sha1.Proofs.MemoryRoutines.Stos.Operation

namespace Sha1.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def repStosForm [Bindings] (kind : Kind) (ip : BitVec 64) (ctx : Instruction_Context) :
    X86.Runtime.SpecM X86.Exception RamState Unit :=
  match kind with
  | .byte => X86.Instructions.REP_STOSB_0 ip ctx
  | .qword => X86.Instructions.REP_STOSQ_0 ip ctx

theorem rep_stos_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : kind = .qword → ctx.rex_w = 1)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hdst : (rdi.read t).toNat + kind.bytes ≤ 2^32)
    (hdstMem : ∀ i < kind.bytes, (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (repStosForm kind ip ctx).run t =
      (.ok (), repCount (stosSpec (8 * kind.bytes) { t with Next_IP := ip })) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) (8 * kind.bytes) (by cases kind <;> simp [Kind.bytes]) ctx
    hes hdf (by simpa using hdst) (by simpa using hdstMem)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  cases kind <;>
  · dsimp only [repStosForm]
    first | unfold X86.Instructions.REP_STOSB_0 | unfold X86.Instructions.REP_STOSQ_0
    try rw [hw rfl]
    simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show ((1 : BitVec 1) == 0) = false from rfl]
    rw [specM_bind_run (modify (fun a : RamState ↦ { a with Next_IP := ip })) _ (s := t) rfl]
    simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
      show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
    rw [specM_bind_run _ _ (rcx_run _)]
    refine (specM_bind_run _ _ (hslice _ _)).trans ?_
    rw [hnz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ _ _ (by
      simp only [X86.Runtime.Unsigned]
      have := BitVec.toNat_ne_iff_ne.mpr hcount
      simp at this ⊢
      omega))]
    simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl,
      List.forIn_cons, List.forIn_nil, bind_assoc]
    refine (specM_bind_run _ _ hop).trans ?_
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
    rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
    simp only [pure_bind]
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
    rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
    rfl

theorem rep_stos_form_zero [Bindings] (kind : Kind) (t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : kind = .qword → ctx.rex_w = 1)
    (hcount : rcx.read t = 0) :
    (repStosForm kind ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  cases kind <;>
  · dsimp only [repStosForm]
    first | unfold X86.Instructions.REP_STOSB_0 | unfold X86.Instructions.REP_STOSQ_0
    try rw [hw rfl]
    simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show ((1 : BitVec 1) == 0) = false from rfl]
    rw [specM_bind_run (modify (fun a : RamState ↦ { a with Next_IP := ip })) _ (s := t) rfl]
    simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
      show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
    rw [specM_bind_run _ _ (rcx_run _)]
    refine (specM_bind_run _ _ (hslice _ _)).trans ?_
    have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
    rw [hz]
    simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
    rw [specM_bind_run (modify (fun a : RamState ↦ { a with Repeat_String_Operation := false })) _
      (s := { t with Next_IP := ip }) rfl]
    rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
    have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
    rw [hz']
    rfl

end Sha1.Proofs.MemoryRoutines.Stos
