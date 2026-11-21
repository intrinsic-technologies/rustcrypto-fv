import P256.Proofs.Sec1.Affine.State
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Routed s t 5) (rip : t.RIP = 0x11020f) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x110214 ∧
      u.regValue .rdi = 0 ∧ u.regValue .r13 = 0 ∧
      AgreesExcept [.reg 13, .reg 7, .flags, .rip] t u := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (xor_r32_r32_rex_effect_step 0x11020f 0x45 0xed (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x1020f _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10212 (by decide)))
  change (xorR32R32Effect 0x11020f 3 13 13 t).Holds t a at effectA
  have agreesA : AgreesExcept [.reg 13, .flags, .rip] t a := effectA.agrees
  have frameA := state.toFrameState.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (xor_r32_r32_effect_step 0x110212 0xff rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0x10212 _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10214 (by decide)))
  change (xorR32R32Effect 0x110212 2 7 7 a).Holds a u at effectU
  have agreesU : AgreesExcept [.reg 7, .flags, .rip] a u := effectU.agrees
  have zeroA : a.regValue .r13 = 0 := by
    have h := effectA.writes
    change a.regValue .r13 = (((t.regValue .r13).setWidth 32) ^^^ ((t.regValue .r13).setWidth 32)).setWidth 64 at h
    rw [BitVec.xor_self] at h
    exact h.trans (by decide +kernel)
  have zeroU : u.regValue .rdi = 0 := by
    have h := effectU.writes
    change u.regValue .rdi = (((a.regValue .rdi).setWidth 32) ^^^ ((a.regValue .rdi).setWidth 32)).setWidth 64 at h
    rw [BitVec.xor_self] at h
    exact h.trans (by decide +kernel)
  exact ⟨u, runA.trans runU, frameA.after_registers readyU agreesU
    (by simp [Component.Covers]) (by simp), effectU.rip, zeroU,
    (agreesU.read (n := 64) (r := 13) (by simp)).trans zeroA,
    (agreesA.trans agreesU).mono (by simp)⟩

end P256.Proofs.Sec1.Affine.Compact
