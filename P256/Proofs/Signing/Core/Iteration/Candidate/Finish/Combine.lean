import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.MovzxByte

import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)
open P256.Proofs.Common.Instructions.MovzxByte

theorem combine [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10cbda)
    (al : (t.regValue .rax).setWidth 8 = 1)
    (bl : (t.regValue .r12).setWidth 8 = 1) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧
      u.RIP = 0x10cbe0 ∧ u.regValue .rdi = 1 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (and_r8_r8_rex_effect_step 0x10cbda 0x44 0xe0 (by simp [RexPrefix]) rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xcbda _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcbdd (by decide)))
  have agreesA : AgreesExcept [.reg 0, .flags, .rip] t a := effectA.agrees
  have frameA := after_registers frame readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (movzx_r32_r8_effect_step 0x10cbdd 0xf8 rfl (by decide)).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xcbdd _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcbe0 (by decide)))
  have agreesU : AgreesExcept [.reg 7, .rip] a u := effectU.agrees
  have agrees : AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u :=
    (agreesA.trans agreesU).mono (by simp)
  refine ⟨u, runA.trans runU, after_registers frame readyU agrees
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp), effectU.rip, ?_, agrees⟩
  have hv := effectU.writes
  change u.regValue .rdi = ((a.regValue .rax).setWidth 8).setWidth 64 at hv
  have ha : a.regValue .rax = mergeGPR 8
      ((t.regValue .rax).setWidth 8 &&& (t.regValue .r12).setWidth 8) (t.regValue .rax) :=
    effectA.writes
  rw [hv, ha, mergeGPR_low8, al, bl]
  rfl

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish
