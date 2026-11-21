import P256.Proofs.Common.CFG.Simulation
import X86Proofs.Program.Execution
import X86Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse
import Prelude.Execution.Termination

namespace P256.Proofs.CFG

open X86 X86.Machine X86.UserProcess X86Proofs

section Machine

variable [Bindings] {boundary : ReturnBoundary}

def machine (boundary : ReturnBoundary) : Semantics where
  State := RamState
  Output := RamState
  Step s t := ∃ n, Advances boundary n s t
  Ret s t := ∃ n, Returns boundary n s t

theorem machine_reaches_iff {s t : (machine boundary).State} :
    (machine boundary).Reaches s t ↔ ∃ n, Advances boundary n s t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, (advances_zero _ _ _).mpr rfl⟩
    | step hs _ ih =>
      obtain ⟨m, hm⟩ := hs
      obtain ⟨n, hn⟩ := ih
      exact ⟨m + n, hm.trans hn⟩
  · rintro ⟨n, h⟩
    exact .step ⟨n, h⟩ (.refl _)

theorem machine_exec_iff {s t : (machine boundary).State} :
    (machine boundary).Exec s t ↔ ∃ n, Returns boundary n s t := by
  constructor
  · intro h
    induction h with
    | ret hr => exact hr
    | step hs _ ih =>
      obtain ⟨m, hm⟩ := hs
      obtain ⟨n, hn⟩ := ih
      exact ⟨m + n, hm.returns hn⟩
  · rintro ⟨n, h⟩
    exact .ret ⟨n, h⟩

theorem machine_segment_exec_iff {s t : (machine boundary).State} :
    (machine boundary).segment.Exec s t ↔ ∃ n, Advances boundary n s t :=
  Semantics.segment_exec_iff.trans machine_reaches_iff

def ReturnOutside (boundary : ReturnBoundary) (code : CodeMap) : Prop :=
  ∀ x ∈ code, x.1 ≠ boundary.rip

def machineAnyReturn (boundary : ReturnBoundary) : Semantics where
  State := RamState
  Output := RamState
  Step s t := ∃ n, Advances boundary n s t
  Ret s t := ∃ n, (Advances boundary n s t ∧ ¬ AtBoundary boundary t) ∨ Returns boundary n s t

end Machine

end P256.Proofs.CFG

namespace P256.Proofs.Simulation

open X86Proofs

open X86 X86.Machine X86.UserProcess CFG

variable [Bindings] {boundary : ReturnBoundary} {hi : Semantics} {R : hi.State → RamState → Prop}
  {post : hi.Output → RamState → Prop}

theorem toMachine (sim : Simulation (machineAnyReturn boundary) hi R post)
    (h : ∀ o t, post o t → AtBoundary boundary t) : Simulation (machine boundary) hi R post where
  step hx hs := sim.step hx hs
  ret hx hr := by
    obtain ⟨o', he, hp⟩ := sim.ret hx hr
    obtain ⟨u, hu, n, hret⟩ := Semantics.exec_iff.mp he
    exact ⟨o', Semantics.Reaches.exec (L := machine boundary) hu
      (.ret ⟨n, hret.resolve_left fun h' => h'.2 (h _ _ hp)⟩), hp⟩

theorem toSegment (sim : Simulation (machineAnyReturn boundary) hi R post)
    (h : ∀ o t, post o t → ¬ AtBoundary boundary t) :
    Simulation (machine boundary).segment hi R post where
  step hx hs := sim.step hx hs
  ret hx hr := by
    obtain ⟨o', he, hp⟩ := sim.ret hx hr
    obtain ⟨u, hu, n, hret⟩ := Semantics.exec_iff.mp he
    rcases hret with ⟨hadv, -⟩ | hret
    · exact ⟨o', Semantics.segment_exec_iff.mpr
        (Semantics.Reaches.tail (L := machine boundary) hu ⟨n, hadv⟩), hp⟩
    · exact absurd (Returns.atBoundary hret) (h _ _ hp)

end P256.Proofs.Simulation

namespace P256.Proofs.CFG

open X86 X86.Machine X86.UserProcess X86Proofs

section CFGMachine

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {program : Program Op Label signature results} {dialect : Dialect Op Value Store} [Bindings]
  {boundary : ReturnBoundary}
  {R : CFG.State Value Store Label signature results → RamState → Prop}
  {post : Output Value Store results → RamState → Prop}

abbrev MachineSimulation (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) : Prop :=
  Simulation (machine boundary) (program.sem dialect) R post

abbrev MachineSegmentSimulation (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) : Prop :=
  Simulation (machine boundary).segment (program.sem dialect) R post

def Outcome.MatchedByMachine (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) (s : RamState) :
    Outcome Value Store Label signature results → Prop
  | .next state => ∃ n t, Advances boundary n s t ∧ R state t
  | .done output => ∃ n t, Returns boundary n s t ∧ post output t
  | .stuck => True

def Outcome.MatchedBySegment (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) (s : RamState) :
    Outcome Value Store Label signature results → Prop
  | .next state => ∃ n t, Advances boundary n s t ∧ R state t
  | .done output => ∃ n t, Advances boundary n s t ∧ post output t
  | .stuck => True

def MachineSimulation.BlockSimulation (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) (label : Label) : Prop :=
  ∀ (arguments : Values Value (signature label)) (store : Store)
    (stack : List (StackFrame Value Label signature results)) (s : RamState),
    R ⟨⟨label, arguments, store⟩, stack⟩ s →
      (program.step dialect ⟨⟨label, arguments, store⟩, stack⟩).MatchedByMachine boundary R post s

def MachineSegmentSimulation.BlockSimulation (program : Program Op Label signature results)
    (dialect : Dialect Op Value Store) (boundary : ReturnBoundary)
    (R : CFG.State Value Store Label signature results → RamState → Prop)
    (post : Output Value Store results → RamState → Prop) (label : Label) : Prop :=
  ∀ (arguments : Values Value (signature label)) (store : Store)
    (stack : List (StackFrame Value Label signature results)) (s : RamState),
    R ⟨⟨label, arguments, store⟩, stack⟩ s →
      (program.step dialect ⟨⟨label, arguments, store⟩, stack⟩).MatchedBySegment boundary R post s

namespace Outcome

variable {s s' : RamState} {t : Outcome Value Store Label signature results}

theorem MatchedByMachine.advances {m : Nat} (h : Advances boundary m s s')
    (hm : t.MatchedByMachine boundary R post s') : t.MatchedByMachine boundary R post s := by
  cases t with
  | next state =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨m + n, u, h.trans hadv, hu⟩
  | done output =>
    obtain ⟨n, u, hret, hu⟩ := hm
    exact ⟨m + n, u, h.returns hret, hu⟩
  | stuck => trivial

theorem MatchedBySegment.advances {m : Nat} (h : Advances boundary m s s')
    (hm : t.MatchedBySegment boundary R post s') : t.MatchedBySegment boundary R post s := by
  cases t with
  | next state =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨m + n, u, h.trans hadv, hu⟩
  | done output =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨m + n, u, h.trans hadv, hu⟩
  | stuck => trivial

theorem MatchedByMachine.toMatchedBy (hm : t.MatchedByMachine boundary R post s) :
    t.MatchedBy (machine boundary) R post s := by
  cases t with
  | next state =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨u, .step ⟨n, hadv⟩ (.refl _), hu⟩
  | done output =>
    obtain ⟨n, u, hret, hu⟩ := hm
    exact ⟨u, .ret ⟨n, hret⟩, hu⟩
  | stuck => trivial

theorem MatchedBySegment.toMatchedBy (hm : t.MatchedBySegment boundary R post s) :
    t.MatchedBy (machine boundary).segment R post s := by
  cases t with
  | next state =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨u, .step ⟨n, hadv⟩ (.refl _), hu⟩
  | done output =>
    obtain ⟨n, u, hadv, hu⟩ := hm
    exact ⟨u, machine_segment_exec_iff.mpr ⟨n, hadv⟩, hu⟩
  | stuck => trivial

end Outcome

theorem MachineSimulation.of_blocks
    (h : ∀ label, MachineSimulation.BlockSimulation program dialect boundary R post label) :
    MachineSimulation program dialect boundary R post :=
  Simulation.of_blocks fun label arguments store stack s hs =>
    (h label arguments store stack s hs).toMatchedBy

theorem MachineSegmentSimulation.of_blocks
    (h : ∀ label, MachineSegmentSimulation.BlockSimulation program dialect boundary R post label) :
    MachineSegmentSimulation program dialect boundary R post :=
  Simulation.of_blocks fun label arguments store stack s hs =>
    (h label arguments store stack s hs).toMatchedBy

theorem MachineSimulation.execution (sim : MachineSimulation program dialect boundary R post)
    {state : CFG.State Value Store Label signature results} {output : Output Value Store results}
    (h : program.Exec dialect state output) (s : RamState) (hs : R state s) :
    ∃ n t, Returns boundary n s t ∧ post output t := by
  obtain ⟨t, he, hp⟩ := Simulation.exec sim h.sem hs
  obtain ⟨n, hn⟩ := machine_exec_iff.mp he
  exact ⟨n, t, hn, hp⟩

theorem MachineSegmentSimulation.execution
    (sim : MachineSegmentSimulation program dialect boundary R post)
    {state : CFG.State Value Store Label signature results} {output : Output Value Store results}
    (h : program.Exec dialect state output) (s : RamState) (hs : R state s) :
    ∃ n t, Advances boundary n s t ∧ post output t := by
  obtain ⟨t, he, hp⟩ := Simulation.exec sim h.sem hs
  obtain ⟨n, hn⟩ := machine_segment_exec_iff.mp he
  exact ⟨n, t, hn, hp⟩

end CFGMachine

section MachineCalls

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  [Bindings] {boundary : ReturnBoundary}
  {R : CFG.State Value Store Label signature results → RamState → Prop}
  {post : Output Value Store results → RamState → Prop}
  {α β : Type} {Entry : α → RamState → Prop} {f : α → β} {Done : β → RamState → Prop}

theorem Summary.matchedByMachine (h : Summary (machine boundary) Entry f Done) {m : Nat}
    {s s₁ : RamState} {a : α} (hpre : Advances boundary m s s₁) (he : Entry a s₁)
    {t : Outcome Value Store Label signature results}
    (hrest : ∀ u, Done (f a) u → t.MatchedByMachine boundary R post u) :
    t.MatchedByMachine boundary R post s := by
  obtain ⟨u, hu, hd⟩ := h a s₁ he
  obtain ⟨n, hn⟩ := machine_reaches_iff.mp hu
  exact Outcome.MatchedByMachine.advances hpre (Outcome.MatchedByMachine.advances hn (hrest u hd))

theorem Summary.matchedBySegment (h : Summary (machine boundary) Entry f Done) {m : Nat}
    {s s₁ : RamState} {a : α} (hpre : Advances boundary m s s₁) (he : Entry a s₁)
    {t : Outcome Value Store Label signature results}
    (hrest : ∀ u, Done (f a) u → t.MatchedBySegment boundary R post u) :
    t.MatchedBySegment boundary R post s := by
  obtain ⟨u, hu, hd⟩ := h a s₁ he
  obtain ⟨n, hn⟩ := machine_reaches_iff.mp hu
  exact Outcome.MatchedBySegment.advances hpre (Outcome.MatchedBySegment.advances hn (hrest u hd))

end MachineCalls

def RoutineReturns (bindings : Bindings) (initial : RamState) (post : RamState → Prop) : Prop :=
  ∃ fuel final, Prelude.UniqueExecution initial fuel final ∧ post final

theorem RoutineReturns.of_simulation [bindings : Bindings] {initial : RamState}
    {boundary : ReturnBoundary} (hb : Prelude.nearReturn64Boundary initial = .ok boundary)
    {hi : Semantics} {R : hi.State → RamState → Prop} {post : hi.Output → RamState → Prop}
    (sim : Simulation (machine boundary) hi R post)
    {x : hi.State} {o : hi.Output} (hexec : hi.Exec x o) (hentry : R x initial) :
    RoutineReturns bindings initial (post o) := by
  obtain ⟨final, he, hpost⟩ := sim.exec hexec hentry
  obtain ⟨n, hn⟩ := machine_exec_iff.mp he
  obtain ⟨fuel, hunique⟩ := Returns.unique_of_boundary hb hn
  exact ⟨fuel, final, hunique, hpost⟩

section

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {program : Program Op Label signature results} {dialect : Dialect Op Value Store}

theorem RoutineReturns.of_cfg [bindings : Bindings] {initial : RamState}
    {boundary : ReturnBoundary} (hb : Prelude.nearReturn64Boundary initial = .ok boundary)
    {R : CFG.State Value Store Label signature results → RamState → Prop}
    {post : Output Value Store results → RamState → Prop}
    (sim : MachineSimulation program dialect boundary R post)
    {state : CFG.State Value Store Label signature results} {output : Output Value Store results}
    (hexec : program.Exec dialect state output) (hentry : R state initial) :
    RoutineReturns bindings initial (post output) :=
  of_simulation hb sim hexec.sem hentry

end

theorem RoutineReturns.mono {bindings : Bindings} {initial : RamState}
    {post post' : RamState → Prop} (h : RoutineReturns bindings initial post)
    (hpost : ∀ final, post final → post' final) : RoutineReturns bindings initial post' :=
  let ⟨fuel, final, hu, hp⟩ := h
  ⟨fuel, final, hu, hpost final hp⟩

structure MachineInvariant [Bindings] {n : Nat} (original : RamState)
    (regions : Vector Prelude.MemoryRegion n) (s : RamState) : Prop where
  ready : ReadyToStep s
  sse : Prelude.SupportedSSE Bindings.processor s
  written : Prelude.MemoryWriteFrame original s regions
  direction : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

namespace MachineInvariant

variable [Bindings] {n : Nat} {original s t : RamState} {regions : Vector Prelude.MemoryRegion n}

theorem supported (h : MachineInvariant original regions s) :
    Prelude.SupportedIntegerMachineState Bindings.processor s :=
  h.ready.supported h.sse

theorem initial (hready : ReadyToStep s) (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hdf : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS) : MachineInvariant s regions s :=
  ⟨hready, hsse, memoryWriteFrame_refl s regions, hdf⟩

theorem of_entryReady {code : CodeMap} (h : EntryReady code s)
    (hdf : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS) : MachineInvariant s regions s :=
  initial h.ready h.sse hdf

theorem of_writeFrame (h : MachineInvariant original regions s) (hready : ReadyToStep t)
    (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hwritten : Prelude.MemoryWriteFrame s t regions)
    (hdf : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS) : MachineInvariant original regions t :=
  ⟨hready, hsse, memoryWriteFrame_trans h.written hwritten, hdf⟩

theorem of_agreesExcept {cs : List Component} (h : MachineInvariant original regions s)
    (hready : ReadyToStep t) (hag : AgreesExcept cs s t) (hw : WritesWithin cs regions)
    (hdf : Component.df ∉ cs) :
    MachineInvariant original regions t :=
  h.of_writeFrame hready (SupportedSSE.of_agreesExcept hag h.sse) (hag.memoryWriteFrame hw)
    (hag.directionFlagClear hdf h.direction)

end MachineInvariant

def RoutineResult (bindings : Bindings) (initial : RamState) {n : Nat}
    (regions : Vector Prelude.MemoryRegion n) (post : RamState → Prop) : Prop :=
  ∃ fuel final, Prelude.UniqueExecution initial fuel final ∧
    Prelude.SupportedIntegerMachineState bindings.processor final ∧
    Prelude.MemoryWriteFrame initial final regions ∧
    Prelude.RFLAGS.DirectionFlagClear final.RFLAGS ∧ post final

theorem RoutineResult.of_routineReturns [bindings : Bindings] {initial : RamState} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} {post : RamState → Prop}
    (h : RoutineReturns bindings initial fun t => MachineInvariant initial regions t ∧ post t) :
    RoutineResult bindings initial regions post :=
  let ⟨fuel, final, hu, hinv, hp⟩ := h
  ⟨fuel, final, hu, hinv.supported, hinv.written, hinv.direction, hp⟩

theorem RoutineResult.of_simulation [bindings : Bindings] {initial : RamState} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} {boundary : ReturnBoundary}
    (hb : Prelude.nearReturn64Boundary initial = .ok boundary) {hi : Semantics}
    {R : hi.State → RamState → Prop} {post : hi.Output → RamState → Prop}
    (sim : Simulation (machine boundary) hi R
      fun o t => MachineInvariant initial regions t ∧ post o t)
    {x : hi.State} {o : hi.Output} (hexec : hi.Exec x o) (hentry : R x initial) :
    RoutineResult bindings initial regions (post o) :=
  RoutineResult.of_routineReturns (RoutineReturns.of_simulation hb sim hexec hentry)

theorem RoutineResult.mono {bindings : Bindings} {initial : RamState} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} {post post' : RamState → Prop}
    (h : RoutineResult bindings initial regions post) (hpost : ∀ final, post final → post' final) :
    RoutineResult bindings initial regions post' :=
  let ⟨fuel, final, hu, hs, hw, hd, hp⟩ := h
  ⟨fuel, final, hu, hs, hw, hd, hpost final hp⟩

end P256.Proofs.CFG
