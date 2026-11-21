import K256.Proofs.Common.OutputExecution

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift

private theorem advances_prefix [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel total : Nat} (run : Advances boundary total s t) (bound : fuel ≤ total) :
    ∃ u, Advances boundary fuel s u := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  change runSteps (Runner.step boundary) (fuel + extra) s = some (.outOfFuel t) at run
  rw [runSteps_add] at run
  cases front : runSteps (Runner.step boundary) fuel s with
  | none => simp [front] at run
  | some result =>
    cases result with
    | outOfFuel u => exact ⟨u, front⟩
    | returned u => simp [front] at run
    | ended success u => simp [front] at run
    | failed failure => simp [front] at run
    | reachedOSEntry entry u => simp [front] at run

theorem neverReturns_of_lifted_progress [bindings : Bindings] {initial : RamState}
    {routine : Routine} {inputs : List ByteArray} {args : List Nat}
    {P : Lifted} {entry : P.Label} {I : P.State → Prop}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall routine initial inputs args)
    (address : P.address entry = routine.entryAddress)
    (blocks : ∀ l, LiftedBlock Extracted.programImage P l)
    {start : P.State}
    (prefixRun : (P.program.sem (dialect Extracted.programImage)).Reaches
      ⟨P.locationOf entry initial, []⟩ start) (hinv : I start)
    (progress : ∀ x, I x → ∃ mid next,
      (P.program.sem (dialect Extracted.programImage)).Reaches x mid ∧
      P.address x.location.label ≠ P.address mid.location.label ∧
      (P.program.sem (dialect Extracted.programImage)).Reaches mid next ∧ I next) :
    NeverReturns initial := by
  let b := returnBoundary initial
  have ready := entryReady bindings hBindings hMachine hCall.programLoaded
  refine ⟨b, nearReturn64Boundary_eq initial ready.ready.dataReady hMachine.integer.ss
    (stack_return_readable hCall.stackAvailable), ?_⟩
  obtain ⟨ret, slot, _, outside⟩ := hCall.returnAddress
  have hret : b.rip = ret := Refine.memLoad_returnSlot slot
  have hb : ReturnOutside b Extracted.programImage := by
    intro x hx
    rw [hret]
    rintro rfl
    exact outside ⟨x.2, programSections_fetchByte_of_mem hx⟩
  have sim := Lifted.simulation blocks hb
  have advance {x y : P.State} {s : RamState}
      (path : (P.program.sem (dialect Extracted.programImage)).Reaches x y)
      (rel : Rel Extracted.programImage P x s) :
      ∃ n t, Advances b n s t ∧ Rel Extracted.programImage P y t := by
    obtain ⟨t, ht, rt⟩ := sim.reaches path rel
    have convert {u v : (machineAnyReturn b).State} (h : (machineAnyReturn b).Reaches u v) :
        ∃ n, Advances b n u v := by
      induction h with
      | refl => exact ⟨0, (advances_zero ..).2 rfl⟩
      | step hs _ ih =>
        obtain ⟨n, hn⟩ := hs
        obtain ⟨m, hm⟩ := ih
        exact ⟨n + m, hn.trans hm⟩
    obtain ⟨n, hn⟩ := convert ht
    exact ⟨n, t, hn, rt⟩
  have unbounded (n : Nat) : ∀ x s, I x → Rel Extracted.programImage P x s →
      ∃ m t, n ≤ m ∧ Advances b m s t := by
    induction n with
    | zero =>
      intro x s _ _
      exact ⟨0, s, Nat.zero_le _, (advances_zero ..).2 rfl⟩
    | succ n ih =>
      intro x s hx rel
      obtain ⟨mid, next, first, moved, rest, hnext⟩ := progress x hx
      obtain ⟨a, u, ha, ru⟩ := advance first rel
      have positive : 0 < a := by
        cases a with
        | zero =>
          have same := (advances_zero ..).mp ha
          exact False.elim (moved (rel.rip.symm.trans (same ▸ ru.rip)))
        | succ => exact Nat.zero_lt_succ _
      obtain ⟨c, v, hc, rv⟩ := advance rest ru
      obtain ⟨m, t, bound, run⟩ := ih next v hnext rv
      exact ⟨a + c + m, t, by omega, (ha.trans hc).trans run⟩
  obtain ⟨m, s, front, rel⟩ := advance prefixRun
    (Rel.locationOf ready (hCall.atEntryPoint.trans address.symm))
  intro fuel
  obtain ⟨n, t, bound, run⟩ := unbounded fuel start s hinv rel
  obtain ⟨u, hu⟩ := advances_prefix (front.trans run) (by omega : fuel ≤ m + n)
  exact ⟨u, hu, List.not_mem_nil⟩

end K256.Proofs.Common
