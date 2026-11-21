import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.XCopy
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Blocks

theorem x_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11095f) : XCopyPre t := by
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
    exact ScalarFrame.stack_code pre.toCalleePre state (codeOffset := 0x1095f)
      (by decide) bound (by decide)

theorem x_copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (xCopyEffect t).Holds t u) : Frame s u := by
  apply stack_effect_frame pre state ready effect.agrees
  · intro c hc hm
    simp only [xCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
    · exact ⟨168,8,rfl,by decide⟩
    · exact ⟨176,8,rfl,by decide⟩
    · exact ⟨184,8,rfl,by decide⟩
    · exact ⟨192,8,rfl,by decide⟩
  all_goals simp [xCopyEffect, Effect.components]

theorem x_copy_byte {t u : RamState} (effect : (xCopyEffect t).Holds t u)
    {off len : Nat} (bound : off+len ≤ 2^64)
    (apart : ∀ a n, (a,n) ∈ ([(168, 8), (176, 8), (184, 8), (192, 8)] : List (Nat × Nat)) →
      a+n ≤ off ∨ off+len ≤ a) {i : Nat} (hi : i < len) :
    u.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply effect_byte effect.agrees bound ?_ hi
  intro c hc hm
  simp only [xCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
  · exact ⟨168,8,rfl,by decide,apart 168 8 (by simp)⟩
  · exact ⟨176,8,rfl,by decide,apart 176 8 (by simp)⟩
  · exact ⟨184,8,rfl,by decide,apart 184 8 (by simp)⟩
  · exact ⟨192,8,rfl,by decide,apart 192 8 (by simp)⟩

theorem x_copy_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (effect : (xCopyEffect t).Holds t u)
    (value : Field.MontgomeryAt t (stackPtr t+376) x) :
    Field.MontgomeryAt u (stackPtr t+168) x := by
  apply Field.montgomeryAt_of_memLoad_limbs value.1
  · intro i hi
    exact effect.agrees.grow _ ((ScalarFrame.stack_readable pre.toCalleePre state
      (offset := 168) (len := 32) (by decide) (by decide)).mem i hi)
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
