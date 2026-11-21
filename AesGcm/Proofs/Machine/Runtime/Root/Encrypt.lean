import AesGcm.Proofs.Machine.Runtime.Execution
import AesGcm.Spec.Program

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Proofs.Machine
open AesGcm.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine

theorem root_execution_of_frame
    {bindings : Bindings} {code : CodeMap} {P : Lifted}
    {initial : RamState} {boundary : ReturnBoundary} {loc : P.Location}
    {output : Output Value Ram Reg.count} {m : FrameInfo} {fr : Activation}
    (hpre : m.Pre code fr initial)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hnear : @nearReturn64Boundary _ _ bindings initial = .ok boundary)
    (sim : @Simulation (@machineAnyReturn bindings boundary)
      (P.program.sem (dialect code)) (@Rel bindings code P) (@RetRel bindings code P))
    (hentry : @Rel bindings code P ⟨loc, []⟩ initial)
    (hexec : P.program.Exec (dialect code) ⟨loc, []⟩ output)
    (htag : output.tag = some ⟨64, boundary.rip⟩)
    (hsp : output.values[4] = ⟨64, boundary.rsp⟩)
    (hdone : Atom.All code output.values output.store (m.doneAtoms fr))
    (hfp : m.fpPreserved = [39, 50, 51])
    (hlive : ∀ (r : Nat), r ∈ [4, 22, 39, 50, 51] ++ m.preserved.map Fin.val → Live P.retLive r)
    (hpreserved : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers → r ∈ m.preserved)
    (hlive4 : Live P.retLive 4)
    (hlive0 : Live P.retLive 0) :
    ∃ fuel final,
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      @RetRel bindings code P output final ∧
      output.values[0] = ⟨64, final.regValue .rax⟩ := by
  obtain ⟨fuel, final, hu, hm, hb, hr⟩ :=
    run_of_lifted_execution (P := P) (code := code) hBindings hnear sim hentry hexec htag hsp hlive4
  obtain ⟨hcallee, hdf⟩ := calleeSaved_of_doneAtoms hpre hr hdone hfp hlive hpreserved
  have hrax : output.values[0] = ⟨64, final.regValue .rax⟩ :=
    hr.regs 0 (by decide) hlive0
  exact ⟨fuel, final, hu, hm, hb, hcallee, hdf, hr, hrax⟩

end AesGcm.Proofs.Machine.Runtime
