import P256.Proofs.EcdhWrapper.Scalar.Call
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.Common.Instructions.ByteLogic.Unary

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteLogic

theorem arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x106907) :
    ∃ u, Advances boundary 2 s u ∧ ReadyToStep u ∧ u.RIP = 0x106912 ∧
      u.regValue .rdi = s.regValue .r14 ∧ u.regValue .rsi = stackPtr s+168 ∧
      AgreesExcept [.reg 6,.reg 7,.rip] s u := by
  obtain ⟨a,ha,ra,ea⟩ := (lea_r64_effect_step 0x106907 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6907 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x690f (by decide)))
  have ga : AgreesExcept [.reg 6,.rip] s a := ea.agrees
  have code := ga.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded)
  obtain ⟨u,hu,ru,eu⟩ := (mov_r64_r64_effect_step 0x10690f 0x4c 0xf7
    (by simp [RexWPrefix]) rfl).advances ra
    (programText_slice code 0x690f _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6912 (by decide)))
  have gu : AgreesExcept [.reg 7,.rip] a u := eu.agrees
  exact ⟨u,ha.trans hu,ru,eu.rip,
    eu.writes.trans (ga.read (n := 64) (r := 14) (by simp)),
    (gu.read (n := 64) (r := 6) (by simp)).trans ea.writes,
    (ga.trans gu).mono (by simp)⟩

theorem invert [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x106917) (value : (s.regValue .rax).setWidth 8 = 0) :
    ∃ u, Advances boundary 3 s u ∧ ReadyToStep u ∧ u.RIP = 0x10691e ∧
      u.regValue .rdi = 1 ∧ AgreesExcept [.reg 0,.reg 7,.flags,.rip] s u := by
  obtain ⟨a,ha,ra,ea⟩ := (not_al_effect_step 0x106917).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6917 _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6919 (by decide)))
  have code := ea.agrees.codeIn (by simp [Effect.components,notAlEffect,Component.Covers])
    (programLoaded_codeIn loaded)
  obtain ⟨u,hu,ru,gu,ipu,vu⟩ := Generate.Zero.mask_arguments boundary 0x106919 ra
    (programText_slice code 0x6919 _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x691b (by decide)))
    (boundary_ne_program outside (inProgram_of_textOffset 0x691e (by decide)))
  refine ⟨u,ha.trans hu,ru,ipu,?_,
    (ea.agrees.trans gu).mono (by simp [Effect.components,notAlEffect])⟩
  have ax : a.regValue .rax = mergeGPR 8 (~~~((s.regValue .rax).setWidth 8)) (s.regValue .rax) := ea.writes
  rw [vu,ax,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  change ((~~~((s.regValue .rax).setWidth 8) &&& 1).setWidth 64) = _
  rw [value]
  rfl

end P256.Proofs.EcdhWrapper.Nonzero
