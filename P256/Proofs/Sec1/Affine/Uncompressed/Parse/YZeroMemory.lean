import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YZero
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Blocks

theorem y_zero_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110739) : YZeroPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · exact stack_writable pre state (off := 48) (by decide) (by decide) (by decide)
  · intro off n hn
    have bound : off+n ≤ 760 ∧ 0 < n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega
    exact ScalarFrame.stack_writable pre.toCalleePre state (by decide) bound.1 bound.2
  · intro off n hn
    have bound : off+n ≤ 760 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega
    exact ScalarFrame.stack_code pre.toCalleePre state (codeOffset := 0x10739)
      (by decide) bound (by decide)

theorem y_zero_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (yZeroEffect t).Holds t u) : Frame s u := by
  apply stack_effect_frame pre state ready effect.agrees
  · intro c hc hm
    simp only [yZeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
    · exact ⟨48,1,rfl,by decide⟩
    · exact ⟨168,8,rfl,by decide⟩
    · exact ⟨176,8,rfl,by decide⟩
    · exact ⟨184,8,rfl,by decide⟩
    · exact ⟨192,8,rfl,by decide⟩
  all_goals simp [yZeroEffect, Effect.components]

theorem y_zero_byte {t u : RamState} (effect : (yZeroEffect t).Holds t u)
    {off len : Nat} (bound : off+len ≤ 2^64)
    (apart : ∀ a n, (a,n) ∈ ([(48, 1), (168, 8), (176, 8), (184, 8), (192, 8)] : List (Nat × Nat)) →
      a+n ≤ off ∨ off+len ≤ a) {i : Nat} (hi : i < len) :
    u.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr t+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply effect_byte effect.agrees bound ?_ hi
  intro c hc hm
  simp only [yZeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try { simp only [Component.isMem, Bool.false_eq_true] at hm }
  · exact ⟨48,1,rfl,by decide,apart 48 1 (by simp)⟩
  · exact ⟨168,8,rfl,by decide,apart 168 8 (by simp)⟩
  · exact ⟨176,8,rfl,by decide,apart 176 8 (by simp)⟩
  · exact ⟨184,8,rfl,by decide,apart 184 8 (by simp)⟩
  · exact ⟨192,8,rfl,by decide,apart 192 8 (by simp)⟩

theorem y_zero_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (effect : (yZeroEffect t).Holds t u) : Field.MontgomeryAt u (stackPtr t+168) 0 := by
  apply zero_value pre state (off := 168) (by decide) effect.agrees.grow
  intro j hj
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have h : memLoad u.external (stackPtr t+168) 64 = 0 := effect.writes.2.1
    simpa [BitVec.add_assoc] using h
  · have h : memLoad u.external (stackPtr t+176) 64 = 0 := effect.writes.2.2.1
    simpa [BitVec.add_assoc] using h
  · have h : memLoad u.external (stackPtr t+184) 64 = 0 := effect.writes.2.2.2.1
    simpa [BitVec.add_assoc] using h
  · have h : memLoad u.external (stackPtr t+192) 64 = 0 := effect.writes.2.2.2.2
    simpa [BitVec.add_assoc] using h

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
