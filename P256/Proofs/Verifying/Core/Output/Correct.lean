import P256.Proofs.Verifying.Core.Output.Accept
import P256.Proofs.Verifying.Core.Output.Store
import P256.Proofs.Verifying.Core.Output.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

structure Prepared [Bindings] (s t : RamState) (accepted : Bool) : Prop extends Core.Frame s t where
  rip : t.RIP = 0x10e191
  output : t.regValue .rax = s.regValue .rdi
  tag : t.regValue .rcx = if accepted then 0 else 1
  error : accepted = false → memLoad t.external (s.regValue .rdi + 8) 64 = 0

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {accepted : Bool}
    (pre : Core.Pre s boundary) (state : Core.Frame s t)
    (rip : t.RIP = 0x10e16c)
    (output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi)
    (tag : (t.regValue .rax).setWidth 8 = if accepted then 1 else 0) :
    ∃ u, Advances boundary 5 t u ∧ Prepared s u accepted := by
  obtain ⟨a,runA,readyA,ripA,agreesA⟩ := branch
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip tag
  have frameA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have readable := stack_readable pre.toCalleePre frameA (offset := 384) (len := 8)
    (by decide) (by decide)
  cases accepted
  · obtain ⟨b,runB,readyB,eB⟩ := (mov_r64_m64_effect_step 0x10e17c 0x48
      (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xe17c _
        (by decide) (by decide +kernel)) ⟨ripA,readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe184 (by decide)))
    change (movR64M64Effect 0x10e17c 0 (.sib 4 none 0 (.d32 384)) a).Holds a b at eB
    have frameB := frameA.after_registers readyB eB.agrees
      (by simp [Component.Covers]) (by simp)
    have outputB : b.regValue .rax = s.regValue .rdi := by
      have h : b.regValue .rax = memLoad a.external (stackPtr a+384) 64 := eB.writes
      rw [h,frameA.rsp,memoryA]
      exact output
    obtain ⟨u,runU,readyU,ripU,tagU,errorU,agreesU⟩ := reject_loaded readyB frameB.loaded
      pre.outerBoundary eB.rip
      (by rw [outputB]; exact (output_writable pre.toCalleePre (by decide) frameB.allocated).add 8 (by decide))
      (by intro off len bound; rw [outputB]
          exact P256.Proofs.Common.Instructions.RangeApart.add_left
            (h := output_code pre.toCalleePre bound) 8 (by decide))
    have outU := (agreesU.read (n := 64) (r := 0) (by simp)).trans outputB
    rw [outputB] at agreesU errorU
    have frameU := after_write pre frameB readyU (off := 8) (agreesU.mono (by simp)) (by decide)
    exact ⟨u,(runA.trans runB).trans runU,⟨frameU,ripU,outU,tagU,fun _ => errorU⟩⟩
  · obtain ⟨u,runU,readyU,ripU,tagU,outU,agreesU⟩ :=
      accept readyA frameA.loaded pre.outerBoundary ripA readable
    have frameU := frameA.after_registers readyU agreesU (by simp [Component.Covers]) (by simp)
    refine ⟨u,runA.trans runU,⟨frameU,ripU,?_,tagU,by simp⟩⟩
    rw [outU,frameA.rsp,memoryA]
    exact output

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {accepted : Bool}
    (pre : Core.Pre s boundary) (state : Prepared s t accepted) :
    ∃ u, Advances boundary 1 t u ∧ Core.Frame s u ∧ u.RIP = 0x10e194 ∧
      ResultAt u (s.regValue .rdi) accepted := by
  obtain ⟨u,runU,readyU,ripU,tagU,agreesU⟩ := store
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary state.rip
    (by rw [state.output]
        simpa only [BitVec.add_zero] using
          (output_writable pre.toCalleePre (by decide) state.allocated).add 0 (len := 8) (by decide))
    (by intro off len bound; rw [state.output]
        simpa only [BitVec.add_zero] using P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre.toCalleePre bound) 0 (len := 8) (by decide))
  rw [state.output] at tagU agreesU
  have ag : AgreesExcept [.mem (s.regValue .rdi) 8,.reg 0,.reg 1,.rip] t u :=
    agreesU.mono (by simp)
  have frameU := after_write pre state.toFrameState readyU
    (by simpa only [BitVec.add_zero] using ag) (off := 0) (by decide)
  exact ⟨u,runU,frameU,ripU,⟨tagU.trans state.tag,
    fun h => (preserves_error ag).trans (state.error h)⟩⟩

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {accepted : Bool}
    (pre : Core.Pre s boundary) (state : Core.Frame s t)
    (rip : t.RIP = 0x10e16c)
    (output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi)
    (tag : (t.regValue .rax).setWidth 8 = if accepted then 1 else 0) :
    ∃ n u, Advances boundary n t u ∧ Core.Frame s u ∧ u.RIP = 0x10e194 ∧
      ResultAt u (s.regValue .rdi) accepted := by
  obtain ⟨a,runA,prepared⟩ := prepare pre state rip output tag
  obtain ⟨u,runU,frameU,ripU,result⟩ := finish pre prepared
  exact ⟨6,u,runA.trans runU,frameU,ripU,result⟩

end P256.Proofs.Verifying.Core.Output
