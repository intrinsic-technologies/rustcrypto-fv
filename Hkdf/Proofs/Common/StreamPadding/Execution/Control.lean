import Hkdf.Proofs.Common.StreamPadding.Execution.Effects

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {inputBytes : Nat}

private theorem running_of_local (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) {t : RamState} {fuel : Nat}
    {components : List Component} (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (footprint : WritesWithin components (writes v (stackPtr s)))
    (df : .df ∉ components) : Running initial boundary (regions v initial) t := by
  apply running.of_agrees run ready agrees ?_ (regions_avoids v pre) df
  intro c hc a covered
  obtain ⟨region, member, contains⟩ := footprint c hc a covered
  rw [rsp] at member
  exact writes_within_regions v pre region member a.toNat contains

theorem load (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .entry) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ (Stages.loadEffect v s).Holds s t := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Stages.load_run v boundary pre.outerBoundary
    s (supportedMachine_readyToStep running.machine) (Stages.load_code v running.loaded)
      (load_pre v pre running rsp rip)
  refine ⟨fuel,t,run,ready,?_,effect⟩
  exact running_of_local v pre running rsp run ready effect.agrees
    (fun c hc a covered => (load_noMem v s c hc a covered).elim)
    (by simp [Stages.loadEffect, Effect.components, Write.component, Operand.component])

theorem mark (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .mark)
    (remaining : Nat) (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 remaining)
    (small : remaining < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ (Stages.markEffect v s).Holds s t := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Stages.mark_run v boundary pre.outerBoundary
    s (supportedMachine_readyToStep running.machine) (Stages.mark_code v running.loaded)
      (mark_pre v pre running rsp rip remaining remainder small)
  refine ⟨fuel,t,run,ready,?_,effect⟩
  exact running_of_local v pre running rsp run ready effect.agrees
    (mark_writes v s remaining (local_bounds v pre rsp).2 remainder small)
    (by simp [Stages.markEffect, Effect.components, Write.component, Operand.component])

theorem branch (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rip : s.RIP = v.pc .branch) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧
      t.RIP = (if (s.regValue v.remainingReg).toNat < 8 then v.pc .firstHead else v.pc .length) ∧
      AgreesExcept [.flags,.rip] s t := by
  obtain ⟨t,run,ready,ripT,agrees⟩ := Stages.branch_run v boundary pre.outerBoundary
    (supportedMachine_readyToStep running.machine) (Stages.branch_code v running.loaded) rip
  refine ⟨t,run,ready,?_,ripT,agrees⟩
  exact running.of_agrees run ready agrees (by simp [WritesWithin,Component.Covers])
    (regions_avoids v pre) (by simp)

theorem copy (v : Variant) (last : Bool)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = Stages.copyStart v last) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ (Stages.copyEffect v last s).Holds s t := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Stages.copy_run v last boundary pre.outerBoundary
    s (supportedMachine_readyToStep running.machine) (Stages.copy_code running.loaded v last)
      (copy_pre v last pre running rsp rip)
  refine ⟨fuel,t,run,ready,?_,effect⟩
  exact running_of_local v pre running rsp run ready effect.agrees
    (copy_writes v last s (local_bounds v pre rsp).2)
    (by simp [Stages.copyEffect, Effect.components, Write.component, Operand.component])

theorem zero (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .zero) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ (Stages.zeroEffect v s).Holds s t := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Stages.zero_run v boundary pre.outerBoundary
    s (supportedMachine_readyToStep running.machine) (Stages.zero_code v running.loaded)
      (zero_pre v pre running rsp rip)
  refine ⟨fuel,t,run,ready,?_,effect⟩
  exact running_of_local v pre running rsp run ready effect.agrees
    (zero_writes v s (local_bounds v pre rsp).2)
    (by simp [Stages.zeroEffect, Effect.components, Write.component, Operand.component])

theorem length (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .length) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ (Stages.lengthEffect v s).Holds s t := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Stages.length_run v boundary pre.outerBoundary
    s (supportedMachine_readyToStep running.machine) (Stages.length_code v running.loaded)
      (length_pre v pre running rsp rip)
  refine ⟨fuel,t,run,ready,?_,effect⟩
  exact running_of_local v pre running rsp run ready effect.agrees
    (length_writes v s (local_bounds v pre rsp).2)
    (by simp [Stages.lengthEffect, Effect.components, Write.component, Operand.component])

end Hkdf.Proofs.Common.StreamPadding.Execution
