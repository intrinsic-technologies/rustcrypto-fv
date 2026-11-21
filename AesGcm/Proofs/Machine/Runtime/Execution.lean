import AesGcm.Proofs.Machine.Runtime.Entry
import AesGcm.Proofs.Copied.X86Proofs.Lift.Simulation
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Frame

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG
  X86Proofs.Lift X86Proofs.Refine

theorem run_of_lifted_execution {bindings : Bindings} {code : CodeMap} {P : Lifted}
    {initial : RamState} {boundary : ReturnBoundary} {loc : P.Location} {output : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hnear : @nearReturn64Boundary _ _ bindings initial = .ok boundary)
    (sim : @Simulation (@machineAnyReturn bindings boundary)
      (P.program.sem (dialect code)) (@Rel bindings code P) (@RetRel bindings code P))
    (hentry : @Rel bindings code P ⟨loc, []⟩ initial)
    (hexec : P.program.Exec (dialect code) ⟨loc, []⟩ output)
    (htag : output.tag = some ⟨64, boundary.rip⟩)
    (hsp : output.values[4] = ⟨64, boundary.rsp⟩)
    (hlive : Live P.retLive 4) :
    ∃ fuel final, UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      @RetRel bindings code P output final := by
  let _ : Bindings := bindings
  obtain ⟨final, he, hr⟩ := sim.exec hexec.sem hentry
  have hb : AtBoundary boundary final := by
    constructor
    · exact Value.eq_bits (Option.some.inj (hr.rip.symm.trans htag))
    · exact Value.eq_bits ((hr.regs 4 (by decide) hlive).symm.trans hsp)
  obtain ⟨middle, hsteps, n, hret⟩ := Semantics.exec_iff.mp he
  have hreturns : Returns boundary n middle final :=
    hret.resolve_left (fun ha => ha.2 hb)
  have hmachine : (machine boundary).Exec initial final :=
    Semantics.Reaches.exec (L := machine boundary) hsteps (.ret ⟨n, hreturns⟩)
  obtain ⟨fuel, hfuel⟩ := machine_exec_iff.mp hmachine
  obtain ⟨least, hunique⟩ := Returns.unique_of_boundary hnear hfuel
  exact ⟨least, final, hunique,
    ⟨hr.ready.cpu, hr.sse, hr.ready.memory, hr.ready.ready⟩,
    ⟨hr.ready.smrr, hr.ready.memoryType, hBindings.stringStride, hr.ready.features.lzcnt⟩, hr⟩

theorem calleeSaved_of_doneAtoms {bindings : Bindings} {P : Lifted} {code : CodeMap}
    {m : FrameInfo} {fr : Activation} {initial final : RamState}
    {output : Output Value Ram Reg.count}
    (hpre : m.Pre code fr initial) (hret : @RetRel bindings code P output final)
    (hdone : Atom.All code output.values output.store (m.doneAtoms fr))
    (hfp : m.fpPreserved = [39, 50, 51])
    (hlive : ∀ r ∈ [4, 22, 39, 50, 51] ++ m.preserved.map Fin.val, Live P.retLive r)
    (hpreserved : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers → r ∈ m.preserved) :
    CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  let _ : Bindings := bindings
  obtain ⟨_, hdf, hp, _⟩ := doneAtoms_retRel hret hdone hfp hlive
  refine ⟨?_, hdf⟩
  have hr : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers →
      (Reg.ofIndex r).read final = (Reg.ofIndex r).read initial := fun r hin =>
    (hp r (hpreserved r hin)).trans (hpre.regs r (Activation.calleeSavedNumbers_sub r hin)).symm
  intro r hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Value.eq_bits (hr 3 (by decide))
  · exact Value.eq_bits (hr 5 (by decide))
  · exact Value.eq_bits (hr 12 (by decide))
  · exact Value.eq_bits (hr 13 (by decide))
  · exact Value.eq_bits (hr 14 (by decide))
  · exact Value.eq_bits (hr 15 (by decide))

end AesGcm.Proofs.Machine.Runtime
