import K256.Proofs.Common.CFG.Simulation
import X86Proofs.Program.Execution
import X86Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse
import Prelude.Execution.Termination
namespace K256.Proofs.CFG

open X86 X86.Machine X86.UserProcess X86Proofs

section Machine

variable [Bindings] {boundary : ReturnBoundary}

def machine (boundary : ReturnBoundary) : Semantics where
  State := RamState
  Output := RamState
  Step s t := ∃ n, Advances boundary n s t
  Ret s t := ∃ n, Returns boundary n s t

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

def ReturnOutside (boundary : ReturnBoundary) (code : CodeMap) : Prop :=
  ∀ x ∈ code, x.1 ≠ boundary.rip

def machineAnyReturn (boundary : ReturnBoundary) : Semantics where
  State := RamState
  Output := RamState
  Step s t := ∃ n, Advances boundary n s t
  Ret s t := ∃ n, (Advances boundary n s t ∧ ¬ AtBoundary boundary t) ∨ Returns boundary n s t

end Machine

end K256.Proofs.CFG

namespace K256.Proofs.Simulation

open X86 X86.Machine X86.UserProcess X86Proofs CFG

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

end K256.Proofs.Simulation

namespace K256.Proofs.CFG

open X86 X86.Machine X86.UserProcess X86Proofs

section CFGMachine

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  {program : Program Op Label signature results} {dialect : Dialect Op Value Store} [Bindings]
  {boundary : ReturnBoundary}
  {R : CFG.State Value Store Label signature results → RamState → Prop}
  {post : Output Value Store results → RamState → Prop}

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

end Outcome

end CFGMachine

section MachineCalls

variable {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {results : Nat}
  [Bindings] {boundary : ReturnBoundary}
  {R : CFG.State Value Store Label signature results → RamState → Prop}
  {post : Output Value Store results → RamState → Prop}
  {α β : Type} {Entry : α → RamState → Prop} {f : α → β} {Done : β → RamState → Prop}

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

end

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

end K256.Proofs.CFG
