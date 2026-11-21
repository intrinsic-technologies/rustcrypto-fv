import P256.Proofs.Signing.Core.Iteration.Digest.Callee
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Invert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

def setupEffect (t : RamState) : Effect :=
  { rip := 0x10ccff
    writes := [⟨(.reg 7 : Operand 64),t.regValue .rbp⟩,
      ⟨(.reg 6 : Operand 64),stackPtr t+304⟩,
      ⟨(.reg 3 : Operand 64),stackPtr t+304⟩] }

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10ccf1) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ (setupEffect t).Holds t u := by
  obtain ⟨a,runA,readyA,effectA⟩ :=
    (mov_r64_r64_effect_step 0x10ccf1 0x48 0xef (by simp [RexWPrefix]) rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xccf1 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xccf4 (by decide)))
  have agreesA : AgreesExcept [.reg 7,.rip] t a := effectA.agrees
  have frameA := after_registers frame readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b,runB,readyB,effectB⟩ :=
    (lea_r64_effect_step 0x10ccf4 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xccf4 _ (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xccfc (by decide)))
  have agreesB : AgreesExcept [.reg 3,.rip] a b := effectB.agrees
  have frameB := after_registers frameA readyB agreesB
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨u,runU,readyU,effectU⟩ :=
    (mov_r64_r64_effect_step 0x10ccfc 0x48 0xde (by simp [RexWPrefix]) rfl).advances readyB
      (programText_slice (programLoaded_codeIn frameB.loaded) 0xccfc _
        (by decide) (by decide +kernel)) effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xccff (by decide)))
  have agreesU : AgreesExcept [.reg 6,.rip] b u := effectU.agrees
  have frameU := after_registers frameB readyU agreesU
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have bx : b.regValue .rbx = stackPtr t+304 := by
    have h : b.regValue .rbx = stackPtr a+304 := effectB.writes
    rw [h,frameA.rsp,frame.rsp]
  refine ⟨u,(runA.trans runB).trans runU,frameU,?_⟩
  refine ⟨effectU.rip,?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · exact (agreesU.read (n := 64) (r := 7) (by simp)).trans
        ((agreesB.read (n := 64) (r := 7) (by simp)).trans effectA.writes)
    · exact effectU.writes.trans bx
    · exact (agreesU.read (n := 64) (r := 3) (by simp)).trans bx
  · trivial
  · exact ((agreesA.trans agreesB).trans agreesU).mono (by simp [setupEffect,Effect.components])

end P256.Proofs.Signing.Core.Iteration.Digest.Invert
