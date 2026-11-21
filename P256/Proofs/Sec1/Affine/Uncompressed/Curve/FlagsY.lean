import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import X86Proofs.Instructions.And.Generated.R8M8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Encoding.Parser.CompressedRoute


theorem flagsY_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110bf0) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x110bf7 ∧
      u.regValue .rdi = ((Operand.reg 0 : Operand 8).read t &&&
        memLoad t.external (stackPtr t + 12) 8).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u := by
  obtain ⟨a, runA, readyA, effectA⟩ := (and_r8_m8_effect_step 0x110bf0 0 (by decide) (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10bf0 _
      (by decide) (by decide +kernel)) ⟨rip, ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre state (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10bf4 (by decide)))
  change (andR8M8Effect 0x110bf0 4 0 (.sib 4 none 0 (.d8 12)) t).Holds t a at effectA
  have agreesA : AgreesExcept [.reg 0, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (movzx_r32_al_effect_step 0x110bf4 0xf8 rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0x10bf4 _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10bf7 (by decide)))
  change (movzxAlEffect 0x110bf4 7 a).Holds a u at effectU
  have agreesU : AgreesExcept [.reg 7, .rip] a u := effectU.agrees
  refine ⟨u, runA.trans runU, stateA.after_registers readyU agreesU
    (by simp [Component.Covers]) (by simp), effectU.rip, ?_,
    (agreesA.trans agreesU).mono (by simp)⟩
  have low : (Operand.reg 0 : Operand 8).read a =
      (Operand.reg 0 : Operand 8).read t &&& memLoad t.external (stackPtr t + 12) 8 := by
    change ((Operand.reg 0 : Operand 64).read a).setWidth 8 = _
    rw [effectA.writes, mergeGPR_low8]
    rfl
  exact effectU.writes.trans (congrArg (BitVec.setWidth 64) low)

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
