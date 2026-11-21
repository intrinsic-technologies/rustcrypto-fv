import P256.Proofs.Sec1.Affine.Dispatch.Entry
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem encoding_tag_cases {bytes : ByteArray} (shape : EncodingShape bytes) :
    bytes.data[0]?.getD 0 = 0 ∨ bytes.data[0]?.getD 0 = 2 ∨
    bytes.data[0]?.getD 0 = 3 ∨ bytes.data[0]?.getD 0 = 4 ∨ bytes.data[0]?.getD 0 = 5 := by
  rcases shape with rfl | ⟨_, two | three | five⟩ | ⟨_, four⟩
  · exact .inl rfl
  · simp [two]
  · simp [three]
  · simp [five]
  · simp [four]

theorem range_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Tagged s t (bytes.data[0]?.getD 0)) (rip : t.RIP = 0x1100f0) :
    ∃ u, Advances boundary 1 t u ∧ Tagged s u (bytes.data[0]?.getD 0) ∧
      u.RIP = (if bytes.data[0]?.getD 0 = 0 then 0x110612 else 0x1100f6) := by
  have condition : condHolds 3 (StatusFlags.ofRFLAGS t.RFLAGS) = (bytes.data[0]?.getD 0 == 0) := by
    change (!(StatusFlags.ofRFLAGS t.RFLAGS).CF) = _
    rw [state.carry]
    rcases encoding_tag_cases pre.input.1 with hz | h2 | h3 | h4 | h5
    all_goals first | (rw [hz]; decide +kernel) | (rw [h2]; decide +kernel) |
      (rw [h3]; decide +kernel) | (rw [h4]; decide +kernel) | (rw [h5]; decide +kernel)
  obtain ⟨u, step, ready, effect⟩ := jcc_rel32_effect_step 0x1100f0 3 0x51c t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x100f0
      [0x0f, 0x83, 0x1c, 0x05, 0, 0] (by decide) (by decide +kernel))
    ⟨rip, fun _ => by decide⟩
  have next : u.RIP = (if bytes.data[0]?.getD 0 = 0 then 0x110612 else 0x1100f6) := by
    rw [effect.rip]
    simp only [jccEffect, branchEffect, condition, beq_iff_eq]
    rfl
  have agrees : AgreesExcept [.rip] t u := effect.agrees
  refine ⟨u, Advances.of_step step (.inl ?_),
    ⟨state.toFrameState.after_registers ready agrees (by simp [Component.Covers]) (by simp),
      (agrees.read (n := 64) (r := 3) (by simp)).trans state.output,
      (agrees.read (n := 64) (r := 6) (by simp)).trans state.input,
      (agrees.read (n := 64) (r := 0) (by simp)).trans state.tagRegister,
      (agrees.read (n := 64) (r := 1) (by simp)).trans state.tagCopy, ?_⟩, next⟩
  · rw [next]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10612 (by decide))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100f6 (by decide))
  · have flags : StatusFlags.ofRFLAGS u.RFLAGS = StatusFlags.ofRFLAGS t.RFLAGS :=
      agrees.agree .flags (by simp) rfl
    rw [flags]
    exact state.carry

end P256.Proofs.Sec1.Affine
