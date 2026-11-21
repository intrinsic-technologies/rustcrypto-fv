import P256.Proofs.SHA256.Compression.Execution
import P256.Proofs.SHA256.Compression.Interface
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Safety

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Position where
  rip : BitVec 64
  saved : Bool
  pointers : List (BitVec 5)

structure State (initial model : RamState) (position : Position) : Prop where
  rip : model.RIP = position.rip
  rsp : (Operand.reg 4 : Operand 64).read model = stackPtr initial
  saved : position.saved = true →
    (Operand.mem (stackPtr initial + 24) : Operand 64).read model = initial.regValue .rsi
  pointers : ∀ r ∈ position.pointers,
    (Operand.reg r : Operand 64).read model = initial.regValue .rsi

structure Footprint (initial : RamState) (cs : List Component) : Prop where
  registers : ∀ c ∈ cs, c.isMem = false → c ∈ blockComponents initial
  memory : ∀ x, ∀ c ∈ cs, c.Covers x → ∃ c' ∈ blockComponents initial, c'.Covers x

theorem Footprint.nil (initial : RamState) : Footprint initial [] := by
  constructor <;> simp

theorem Footprint.append {initial : RamState} {xs ys : List Component}
    (hx : Footprint initial xs) (hy : Footprint initial ys) : Footprint initial (xs ++ ys) := by
  constructor
  · intro c hc hm
    rcases List.mem_append.mp hc with hc | hc
    · exact hx.registers c hc hm
    · exact hy.registers c hc hm
  · intro x c hc hm
    rcases List.mem_append.mp hc with hc | hc
    · exact hx.memory x c hc hm
    · exact hy.memory x c hc hm

theorem Footprint.frame {initial actual final : RamState} {cs : List Component}
    (h : Footprint initial cs) (agree : AgreesExcept cs actual final) :
    AgreesExcept (blockComponents initial) actual final :=
  agree.widen h.registers h.memory

theorem State.rsi {initial model : RamState} {position : Position}
    (state : State initial model position) (pointer : 6 ∈ position.pointers) :
    model.regValue .rsi = initial.regValue .rsi := state.pointers 6 pointer

variable [Bindings]

structure StepCertificate (initial : RamState) (instruction : CheckedInstruction)
    (before after : Position) : Prop where
  access : ∀ model, State initial model before → instruction.access initial model
  avoids : ∀ model, State initial model before →
    (instruction.effect model).Avoids Extracted.programSections.toCodeMap
  inside : ∀ model, State initial model before → InProgram (instruction.effect model).rip
  next : ∀ model, State initial model before → State initial (instruction.next model) after
  footprint : ∀ model, State initial model before → Footprint initial (instruction.effect model).components

inductive Certificate (initial : RamState) :
    List CheckedInstruction → Position → Position → List Position → Prop where
  | nil (position : Position) : Certificate initial [] position position []
  | cons {instruction : CheckedInstruction} {rest : List CheckedInstruction}
      {before middle after : Position} {positions : List Position}
      (step : StepCertificate initial instruction before middle)
      (tail : Certificate initial rest middle after positions) :
      Certificate initial (instruction :: rest) before after (middle :: positions)

namespace Certificate

variable {initial : RamState} {instructions : List CheckedInstruction}
  {before after : Position} {positions : List Position}

theorem append {right : List CheckedInstruction} {finish : Position} {more : List Position}
    (left : Certificate initial instructions before after positions)
    (rightCert : Certificate initial right after finish more) :
    Certificate initial (instructions ++ right) before finish (positions ++ more) := by
  induction left with
  | nil => exact rightCert
  | cons step _ ih => exact .cons step (ih rightCert)

theorem result (cert : Certificate initial instructions before after positions)
    (model : RamState) (state : State initial model before) :
    State initial (InstructionTrace.run instructions model) after ∧
      Footprint initial (InstructionTrace.components instructions model) := by
  induction cert generalizing model with
  | nil => exact ⟨state, Footprint.nil _⟩
  | cons step _ ih =>
    obtain ⟨final, footprint⟩ := ih _ (step.next model state)
    exact ⟨final, (step.footprint model state).append footprint⟩

theorem safe (cert : Certificate initial instructions before after positions)
    (model : RamState) (state : State initial model before) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip)
    (covered : ∀ x ∈ InstructionTrace.code instructions, x ∈ Extracted.programSections.toCodeMap) :
    InstructionTrace.Safe initial Extracted.programSections.toCodeMap boundary instructions model := by
  induction cert generalizing model with
  | nil => trivial
  | @cons instruction rest before middle after positions step tail ih =>
    refine ⟨step.access model state, ?_, step.avoids model state,
      P256.Proofs.Program.boundary_ne_program outside (step.inside model state), ?_⟩
    · intro x hx
      apply covered x
      exact List.mem_append_left _ hx
    · apply ih _ (step.next model state)
      intro x hx
      exact covered x (List.mem_append_right _ hx)

end Certificate

end P256.Proofs.SHA256.Compression.Safety
