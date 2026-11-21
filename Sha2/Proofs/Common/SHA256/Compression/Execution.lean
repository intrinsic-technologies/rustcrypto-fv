import Sha2.Proofs.Common.SHA256.Compression.Support
import Sha2.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

def MemoryGrows (s t : RamState) : Prop :=
  ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

structure CheckedInstruction [Bindings] where
  address : BitVec 64
  bytes : List UInt8
  access : RamState → RamState → Prop
  effect : RamState → Effect
  locality : Effect.Local effect
  execute : ∀ (initial model actual : RamState), ReadyToStep actual →
    CodeIn (codeRange address bytes) actual → Obs model actual → model.RIP = actual.RIP →
    MemoryGrows initial actual → access initial model →
    ∃ next, Machine.step actual = some (.next next) ∧ ReadyToStep next ∧
      (effect actual).Holds actual next

namespace CheckedInstruction

variable [Bindings]

def ofStep {p : BitVec 64} {bytes : List UInt8} {pre : RamState → Prop}
    {effect : RamState → Effect} (step : StepEffect pre (codeRange p bytes) effect)
    (locality : Effect.Local effect) (access : RamState → RamState → Prop)
    (transfer : ∀ initial model actual, Obs model actual → model.RIP = actual.RIP →
      MemoryGrows initial actual → access initial model → pre actual) : CheckedInstruction :=
  ⟨p, bytes, access, effect, locality, fun initial model actual ready loaded obs rip grows safe =>
    step actual ready loaded (transfer initial model actual obs rip grows safe)⟩

def register {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    (step : StepEffect (fun s => s.RIP = p) (codeRange p bytes) effect)
    (locality : Effect.Local effect) : CheckedInstruction :=
  ofStep step locality (fun _ model => model.RIP = p)
    (fun _ _ _ _ rip _ safe => rip.symm.trans safe)

def load {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    {addr : RamState → BitVec 64} {count : Nat}
    (step : StepEffect (LoadPre p addr count) (codeRange p bytes) effect)
    (locality : Effect.Local effect)
    (addressLocal : ∀ s t, Obs s t → addr s = addr t) : CheckedInstruction :=
  ofStep step locality (fun initial model => model.RIP = p ∧ MemReadable initial (addr model) count)
    (fun _ _ actual obs rip grows safe =>
      ⟨rip.symm.trans safe.1, by
        rw [← addressLocal _ _ obs]
        exact ⟨safe.2.low, fun i hi => grows _ (safe.2.mem i hi)⟩⟩)

def store {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    {addr : RamState → BitVec 64} {count codeLen : Nat}
    (step : StepEffect (StorePre p codeLen addr count) (codeRange p bytes) effect)
    (locality : Effect.Local effect)
    (addressLocal : ∀ s t, Obs s t → addr s = addr t) : CheckedInstruction :=
  ofStep step locality (fun initial model => model.RIP = p ∧
      MemWritable initial (addr model) count ∧ RangeApart (addr model) count p codeLen)
    (fun _ _ actual obs rip grows safe =>
      ⟨rip.symm.trans safe.1, by
        rw [← addressLocal _ _ obs]
        exact ⟨safe.2.1.low, fun i hi => grows _ (safe.2.1.mem i hi),
          safe.2.1.tables⟩,
        (addressLocal _ _ obs) ▸ safe.2.2⟩)

def next (instruction : CheckedInstruction) (model : RamState) : RamState :=
  { (instruction.effect model).after model true with RIP := (instruction.effect model).rip }

theorem next_obs (instruction : CheckedInstruction) (model actual : RamState)
    (obs : Obs model actual) :
    Obs (instruction.next model) ((instruction.effect actual).after actual true) :=
by
  have h := Effect.after_obs_of obs (instruction.locality.writes model actual obs) true
  exact ⟨h.gpr, h.mem, h.zmm, h.rflags, h.mxcsr, h.fpr, h.fsw, h.ftw, h.fcw, h.fpuPtr, h.cs⟩

end CheckedInstruction

namespace InstructionTrace

variable [Bindings]

def code (instructions : List CheckedInstruction) : CodeMap :=
  instructions.flatMap fun instruction => codeRange instruction.address instruction.bytes

def ordered : BitVec 64 → List CheckedInstruction → Bool
  | _, [] => true
  | address, instruction :: rest =>
    (instruction.address == address) &&
      ordered (address + BitVec.ofNat 64 instruction.bytes.length) rest

theorem code_eq_range (instructions : List CheckedInstruction) (address : BitVec 64)
    (order : ordered address instructions = true) :
    code instructions = codeRange address (instructions.flatMap CheckedInstruction.bytes) := by
  induction instructions generalizing address with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [ordered, Bool.and_eq_true, beq_iff_eq] at order
    simp only [code, List.flatMap_cons]
    rw [show (rest.flatMap fun i => codeRange i.address i.bytes) =
      codeRange (address + BitVec.ofNat 64 instruction.bytes.length)
        (rest.flatMap CheckedInstruction.bytes) from ih _ order.2]
    rw [order.1, codeRange_append]

def run : List CheckedInstruction → RamState → RamState
  | [], model => model
  | instruction :: rest, model => run rest (instruction.next model)

def components : List CheckedInstruction → RamState → List Component
  | [], _ => []
  | instruction :: rest, model =>
    (instruction.effect model).components ++ components rest (instruction.next model)

def Safe (initial : RamState) (code : CodeMap) (boundary : ReturnBoundary) :
    List CheckedInstruction → RamState → Prop
  | [], _ => True
  | instruction :: rest, model =>
    instruction.access initial model ∧
    (∀ x ∈ codeRange instruction.address instruction.bytes, x ∈ code) ∧
    (instruction.effect model).Avoids code ∧
    (instruction.effect model).rip ≠ boundary.rip ∧
    Safe initial code boundary rest (instruction.next model)

theorem run_append (left right : List CheckedInstruction) (model : RamState) :
    run (left ++ right) model = run right (run left model) := by
  induction left generalizing model with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.next model)

theorem components_append (left right : List CheckedInstruction) (model : RamState) :
    components (left ++ right) model =
      components left model ++ components right (run left model) := by
  induction left generalizing model with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append, components, run, ih, List.append_assoc]

theorem safe_append (initial : RamState) (code : CodeMap) (boundary : ReturnBoundary)
    (left right : List CheckedInstruction) (model : RamState) :
    Safe initial code boundary (left ++ right) model ↔
      Safe initial code boundary left model ∧
      Safe initial code boundary right (run left model) := by
  induction left generalizing model with
  | nil => simp only [List.nil_append, Safe, run, true_and]
  | cons instruction rest ih =>
    simp only [List.cons_append, Safe, run, ih, and_assoc]

theorem execute (instructions : List CheckedInstruction) (initial model actual : RamState)
    (code : CodeMap) (boundary : ReturnBoundary)
    (ready : ReadyToStep actual) (loaded : CodeIn code actual)
    (obs : Obs model actual) (rip : model.RIP = actual.RIP)
    (grows : MemoryGrows initial actual)
    (safe : Safe initial code boundary instructions model) :
    ∃ fuel final, Advances boundary fuel actual final ∧ ReadyToStep final ∧ CodeIn code final ∧
      Obs (run instructions model) final ∧ (run instructions model).RIP = final.RIP ∧
      AgreesExcept (components instructions model) actual final := by
  induction instructions generalizing model actual with
  | nil =>
    exact ⟨0, actual, (advances_zero boundary actual actual).mpr rfl, ready, loaded, obs, rip, AgreesExcept.refl [] actual⟩
  | cons instruction rest ih =>
    obtain ⟨access, covered, avoids, outside, safe⟩ := safe
    obtain ⟨next, step, nextReady, effect⟩ := instruction.execute initial model actual ready
      (loaded.mono covered) obs rip grows access
    have avoidsActual := instruction.locality.avoids obs avoids
    have outsideActual : (instruction.effect actual).rip ≠ boundary.rip := by
      rw [← instruction.locality.rip model actual obs]
      exact outside
    have advance : Advances boundary 1 actual next :=
      Advances.of_step step (.inl (effect.rip ▸ outsideActual))
    have nextObs := (instruction.next_obs model actual obs).trans
      (effect.obsAfter (instruction.locality.full actual) true)
    have nextRip : (instruction.next model).RIP = next.RIP :=
      (instruction.locality.rip model actual obs).trans effect.rip.symm
    have nextGrows : MemoryGrows initial next := fun a ha => effect.agrees.grow a (grows a ha)
    obtain ⟨fuel, final, execution, finalReady, finalCode, finalObs, finalRip, frame⟩ :=
      ih (instruction.next model) next nextReady (effect.codeIn avoidsActual loaded)
        nextObs nextRip nextGrows safe
    refine ⟨1 + fuel, final, advance.trans execution, finalReady, finalCode, finalObs,
      finalRip, ?_⟩
    have agree := effect.agrees.trans frame
    have sameComponents := Effect.components_eq (instruction.locality.writes model actual obs)
      (instruction.locality.flagsSome model actual obs)
    simpa only [components, sameComponents] using agree

end InstructionTrace

end Sha2.Proofs.Common.SHA256.Compression
