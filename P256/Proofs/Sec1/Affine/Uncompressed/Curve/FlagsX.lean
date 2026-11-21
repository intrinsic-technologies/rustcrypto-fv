import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Common.Instructions.ByteLogic.AndReg

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Encoding.Parser.CompressedRoute
open P256.Proofs.Common.Instructions.ByteLogic

theorem flagsX_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110be5) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x110beb ∧
      u.regValue .rdi = ((Operand.reg 0 : Operand 8).read t &&&
        (Operand.reg 15 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u := by
  obtain ⟨a, runA, readyA, effectA⟩ := (and_r8_r8_rex_effect_step 0x110be5 0x44 0xf8 (by simp [RexPrefix]) rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10be5 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10be8 (by decide)))
  change (andR8R8Effect 0x110be5 0 15 t).Holds t a at effectA
  have agreesA : AgreesExcept [.reg 0, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (movzx_r32_al_effect_step 0x110be8 0xf8 rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0x10be8 _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10beb (by decide)))
  change (movzxAlEffect 0x110be8 7 a).Holds a u at effectU
  have agreesU : AgreesExcept [.reg 7, .rip] a u := effectU.agrees
  refine ⟨u, runA.trans runU, stateA.after_registers readyU agreesU
    (by simp [Component.Covers]) (by simp), effectU.rip, ?_,
    (agreesA.trans agreesU).mono (by simp)⟩
  have low : (Operand.reg 0 : Operand 8).read a =
      (Operand.reg 0 : Operand 8).read t &&& (Operand.reg 15 : Operand 8).read t := by
    change ((Operand.reg 0 : Operand 64).read a).setWidth 8 = _
    rw [effectA.writes, mergeGPR_low8]
  exact effectU.writes.trans (congrArg (BitVec.setWidth 64) low)

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
