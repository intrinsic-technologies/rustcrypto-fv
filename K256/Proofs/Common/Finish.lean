import K256.Proofs.Common.Machine
import K256.Spec
import K256.Proofs.Common.Lift.Simulation
import K256.Proofs.Common.Refine.Lemma.Frame

namespace K256.Proofs.Common
open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

structure Returned (initial : RamState) {n : Nat} (regions : Vector MemoryRegion n)
    (output : Output Value Ram Reg.count) : Prop where
  tag : output.tag = some ⟨64, (returnBoundary initial).rip⟩
  rsp : output.values[4] = ⟨64, (returnBoundary initial).rsp⟩
  direction : output.values[22] = ⟨1, 0⟩
  preserved : ∀ (r : Fin Reg.count), r.val ∈ [3, 5, 12, 13, 14, 15] →
    output.values[r] = (Reg.ofIndex r).read initial
  written : RamWriteFrame initial.external output.store regions.toList
  status : output.values[0].width = 64

theorem Returned.boundary [Bindings] {code : CodeMap} {P : Lifted} {initial final : RamState}
    {n : Nat} {regions : Vector MemoryRegion n}
    {output : Output Value Ram Reg.count} (h : Returned initial regions output)
    (hr : RetRel code P output final) (hlive : Live P.retLive 4) :
    AtBoundary (returnBoundary initial) final := by
  have hrip : final.RIP = (returnBoundary initial).rip :=
    Value.eq_bits (Option.some.inj (hr.rip.symm.trans h.tag))
  have hrsp : stackPtr final = (returnBoundary initial).rsp :=
    Value.eq_bits ((hr.regs 4 (by decide) hlive).symm.trans h.rsp)
  exact ⟨hrip, hrsp⟩

theorem Returned.memoryFrame [Bindings] {code : CodeMap} {P : Lifted} {initial final : RamState}
    {n : Nat} {regions : Vector MemoryRegion n}
    {output : Output Value Ram Reg.count} (h : Returned initial regions output)
    (hr : RetRel code P output final) : MemoryWriteFrame initial final regions := by
  have hw : RamWriteFrame initial.external final.external regions.toList := hr.store ▸ h.written
  exact hw.memoryWriteFrame fun _ hx r hr => hx r (by simpa only [Vector.mem_toList_iff] using hr)

theorem Returned.calleeSaved [Bindings] {code : CodeMap} {P : Lifted} {initial final : RamState}
    {n : Nat} {regions : Vector MemoryRegion n}
    {output : Output Value Ram Reg.count} (h : Returned initial regions output)
    (hr : RetRel code P output final)
    (hlive : ∀ r ∈ [3, 5, 12, 13, 14, 15], Live P.retLive r) :
    CalleeSavedRegistersUnchanged initial final := by
  intro register hregister
  have hread : ∀ (i : Fin Reg.count) (hi : i.val ∈ [3, 5, 12, 13, 14, 15]),
      (Reg.ofIndex i).read final = (Reg.ofIndex i).read initial := by
    intro i hi
    exact (hr.regs i i.isLt (hlive i hi)).symm.trans (h.preserved i hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Value.eq_bits (hread 3 (by decide))
  · exact Value.eq_bits (hread 5 (by decide))
  · exact Value.eq_bits (hread 12 (by decide))
  · exact Value.eq_bits (hread 13 (by decide))
  · exact Value.eq_bits (hread 14 (by decide))
  · exact Value.eq_bits (hread 15 (by decide))

theorem run_of_lifted_execution {bindings : Bindings} {code : CodeMap} {P : Lifted}
    {initial : RamState} {n : Nat} {regions : Vector MemoryRegion n}
    {loc : P.Location} {output : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hnear : @nearReturn64Boundary _ _ bindings initial = .ok (returnBoundary initial))
    (sim : @Simulation (@machineAnyReturn bindings (returnBoundary initial))
      (P.program.sem (dialect code)) (@Rel bindings code P) (@RetRel bindings code P))
    (hentry : @Rel bindings code P ⟨loc, []⟩ initial)
    (hexec : P.program.Exec (dialect code) ⟨loc, []⟩ output)
    (hpost : Returned initial regions output)
    (hlive : ∀ r ∈ [0, 3, 4, 5, 12, 13, 14, 15, 22], Live P.retLive r) :
    ∃ fuel final, UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      MemoryWriteFrame initial final regions ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      final.external = output.store ∧
      (Reg.ofIndex 0).read final = output.values[0] := by
  letI := bindings
  obtain ⟨final, he, hr⟩ := sim.exec hexec.sem hentry
  have hb := hpost.boundary hr (hlive 4 (by decide))
  obtain ⟨u, hu, steps, hret⟩ := Semantics.exec_iff.mp he
  have hu' : (machine (returnBoundary initial)).Reaches initial u := hu
  have he' : (machine (returnBoundary initial)).Exec initial final :=
    hu'.exec (.ret ⟨steps, hret.resolve_left (fun h => h.2 hb)⟩)
  obtain ⟨steps, hreturns⟩ := machine_exec_iff.mp he'
  obtain ⟨fuel, hu⟩ := Returns.unique_of_boundary hnear hreturns
  have hdf : DirectionFlagUnset final :=
    Reg.read_df_iff.mp ((hr.regs 22 (by decide) (hlive 22 (by decide))).symm.trans hpost.direction)
  refine ⟨fuel, final, hu, hr.ready.supported hr.sse,
    ⟨hr.ready.smrr, hr.ready.memoryType, hBindings.stringStride, hr.ready.features.lzcnt⟩,
    hpost.memoryFrame hr, hpost.calleeSaved hr (fun r hmem => hlive r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
      omega)), hdf, hr.store.symm, ?_⟩
  exact (hr.regs 0 (by decide) (hlive 0 (by decide))).symm

end K256.Proofs.Common
