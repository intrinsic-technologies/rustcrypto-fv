import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YCopy
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Blocks

theorem y_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110790) : YCopyPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro off ho
    have bound : off+8 ≤ 760 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      omega
    exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) bound
  · intro off n hn
    have bound : off+n ≤ 760 ∧ 0 < n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega
    exact ScalarFrame.stack_writable pre.toCalleePre state (by decide) bound.1 bound.2
  · intro off n hn
    have bound : off+n ≤ 760 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega
    exact ScalarFrame.stack_code pre.toCalleePre state (codeOffset := 0x10790)
      (by decide) bound (by decide)

theorem y_copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (yCopyEffect t).Holds t u) : Frame s u := by
  apply stack_effect_frame pre state ready effect.agrees
  · intro c hc hm
    simp only [yCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
    · exact ⟨96,8,rfl,by decide⟩
    · exact ⟨104,8,rfl,by decide⟩
    · exact ⟨112,8,rfl,by decide⟩
    · exact ⟨120,8,rfl,by decide⟩
  all_goals simp [yCopyEffect, Effect.components]

theorem y_copy_byte {t u : RamState} (effect : (yCopyEffect t).Holds t u)
    {off len : Nat} (bound : off+len ≤ 2^64)
    (apart : ∀ a n, (a,n) ∈ ([(96, 8), (104, 8), (112, 8), (120, 8)] : List (Nat × Nat)) →
      a+n ≤ off ∨ off+len ≤ a) {i : Nat} (hi : i < len) :
    u.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply effect_byte effect.agrees bound ?_ hi
  intro c hc hm
  simp only [yCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
  · exact ⟨96,8,rfl,by decide,apart 96 8 (by simp)⟩
  · exact ⟨104,8,rfl,by decide,apart 104 8 (by simp)⟩
  · exact ⟨112,8,rfl,by decide,apart 112 8 (by simp)⟩
  · exact ⟨120,8,rfl,by decide,apart 120 8 (by simp)⟩

theorem y_copy_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (effect : (yCopyEffect t).Holds t u)
    (value : Field.MontgomeryAt t (stackPtr t+168) x) :
    Field.MontgomeryAt u (stackPtr t+96) x := by
  apply Field.montgomeryAt_of_memLoad_limbs value.1
  · intro i hi
    exact effect.agrees.grow _ ((ScalarFrame.stack_readable pre.toCalleePre state
      (offset := 96) (len := 32) (by decide) (by decide)).mem i hi)
  · intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h := value.memLoad_limb 0 (by decide)
      have e := effect.writes.1
      simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat] at h ⊢
      exact e.trans h
    · have h := value.memLoad_limb 1 (by decide)
      have e := effect.writes.2.1
      simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat] at h ⊢
      exact e.trans h
    · have h := value.memLoad_limb 2 (by decide)
      have e := effect.writes.2.2.1
      simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat] at h ⊢
      exact e.trans h
    · have h := value.memLoad_limb 3 (by decide)
      have e := effect.writes.2.2.2.1
      simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat] at h ⊢
      exact e.trans h

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
