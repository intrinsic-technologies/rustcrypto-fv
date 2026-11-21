import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Serialize
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Outer

open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256 Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem serializePre [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat} {regions : Vector MemoryRegion n}
    (pre : ExpandPre entry boundary key info ptr length) (frame : Running entry boundary regions s)
    (sp : stackPtr s = stackPtr entry - 536)
    (phase : Bool) (pc : s.RIP = Serialize.start phase) : Serialize.Pre phase s := by
  have src : Serialize.source phase ≤ 184 := by cases phase <;> decide
  have dst : Serialize.destination phase ≤ 80 := by cases phase <;> decide
  let codeOffset := if phase then 0xf4cb else 0xf3bd
  have codeAddr : Serialize.start phase = Extracted.textAddress + BitVec.ofNat 64 codeOffset := by
    cases phase <;> rfl
  refine ⟨pc, ?_, ?_, ?_⟩
  · intro i hi
    change MemReadable s (stackPtr s + _) 4
    exact local_readable pre.call.stack frame.allocated sp (by omega) (by omega)
  · intro i hi
    change Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + _) 4
    exact local_writable pre.call.stack pre.call.stackAvoid frame.allocated sp (by omega) (by decide)
  · intro i hi
    change RangeApart (stackPtr s + _) 4 (Serialize.start phase) 113
    rw [codeAddr]
    exact local_codeApart pre.call.stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp)) sp
      (by omega) (by omega) (by cases phase <;> decide)

abbrev serializeComponents (phase : Bool) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .rip,
    .mem (stackPtr s + BitVec.ofNat 64 (Serialize.destination phase)) 32]

theorem serializeWrites (phase : Bool) (s : RamState) :
    StackWrites (serializeComponents phase s) (stackPtr s) [(Serialize.destination phase, 32)] := by
  intro c member a covered
  simp only [serializeComponents, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact covered.elim | exact ⟨_, List.mem_singleton_self _, covered⟩

theorem serializeAt [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat} {hash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (phase : Bool) (pc : s.RIP = Serialize.start phase)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 (Serialize.source phase)) hash) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = Serialize.finish phase ∧ stackPtr t = stackPtr s ∧
      AgreesExcept (serializeComponents phase s) s t ∧
      (⟨(stackPtr s + BitVec.ofNat 64 (Serialize.destination phase)).toNat, 32⟩ :
        MemoryRegion).HasBytes t.external (serializeHash hash) := by
  obtain ⟨fuel, t, run, ready, effect, bytes⟩ := Serialize.execute phase
    (supportedMachine_readyToStep saved.machine) saved.loaded pre.call.outerBoundary
    (serializePre pre saved.toRunning saved.sp phase pc) words
  have agrees : AgreesExcept (serializeComponents phase s) s t := Serialize.agreement effect
  have saved' := (serializeWrites phase s).saved pre pos bound saved run ready agrees (by
    intro range member
    obtain rfl := List.mem_singleton.mp member
    cases phase <;> decide) (by simp [serializeComponents])
  exact ⟨fuel, t, run, saved'.1, effect.rip, Serialize.rsp_unchanged effect, agrees, bytes⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Outer
