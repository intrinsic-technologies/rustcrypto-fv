import X86Proofs.Program.Execution
import P256.Proofs.Program.Code

set_option autoImplicit false


namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def clobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 8, .reg 9, .reg 10, .flags, .rip]

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x119270
  leftLength : s.regValue .rsi = 4
  rightLength : s.regValue .rcx = 4
  left : MemReadable s (s.regValue .rdi) 32
  right : MemReadable s (s.regValue .rdx) 32
  returnReadable : MemReadable s (stackPtr s) 8
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (returnBoundary s).rip

structure Result [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = (returnBoundary s).rsp
  agrees : AgreesExcept (clobbers ++ [.reg 4]) s t

theorem Result.memory [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (h : Result s t boundary) : t.external = s.external :=
  h.agrees.external (by simp [clobbers, Component.Covers])

theorem Result.loaded [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (h : Result s t boundary) (loaded : ProgramLoaded s) : ProgramLoaded t := by
  intro a b hb
  rw [h.memory]
  exact loaded a b hb

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  agrees : AgreesExcept clobbers s t

theorem Stage.memory [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (h : Stage s t boundary) : t.external = s.external :=
  h.agrees.external (by simp [clobbers, Component.Covers])

theorem Stage.loaded [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (h : Stage s t boundary) (loaded : ProgramLoaded s) : ProgramLoaded t := by
  intro a b hb
  rw [h.memory]
  exact loaded a b hb

theorem Stage.rsp [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (h : Stage s t boundary) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [clobbers])

theorem Stage.extend [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {fuel : Nat} {e : Effect} (h : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u) (effect : e.Holds t u)
    (subset : ∀ c ∈ e.components, c ∈ clobbers) : Stage s u boundary := by
  obtain ⟨n, hn⟩ := h.execution
  refine ⟨⟨n + fuel, hn.trans run⟩, ready, (h.agrees.trans effect.agrees).mono ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hc
  · exact subset c hc

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
