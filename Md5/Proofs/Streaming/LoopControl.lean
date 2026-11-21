import Md5.Proofs.Streaming.Counter
import Md5.Proofs.Streaming.Invariant

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

structure LoopCounterPost [Bindings] (kind : LoopKind.Kind) (boundary : ReturnBoundary)
    (finish index : Nat) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = if index + 1 < finish then LoopKind.entry kind else LoopKind.finalPC kind
  indexValue : (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read t =
    BitVec.ofNat 64 (index + 1)
  agrees : AgreesExcept [.reg (LoopKind.indexRegister kind), .flags, .rip] s t

def RegisterCounterKind.loopKind : RegisterCounterKind → LoopKind.Kind
  | .slicesPartial | .slicesFull => .slices
  | .resetFirstPartial | .resetFirstFull => .resetFirst
  | .updateFinalizeIntoPartial | .updateFinalizeIntoFull => .updateFinalizeInto
  | .finalizeResetFirstPartial | .finalizeResetFirstFull => .finalizeResetFirst
  | .resetDiscardFirstPartial | .resetDiscardFirstFull => .resetDiscardFirst

theorem register_counter_post [Bindings] (kind : RegisterCounterKind)
    {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    {s : RamState} {finish index : Nat} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP = kind.pc)
    (hIndex : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 index)
    (hCount : (Operand.reg (kind.count.setWidth 5) : Operand 64).read s = BitVec.ofNat 64 finish)
    (hi : index < finish) (hb : finish < 2^64) :
    ∃ t, LoopCounterPost kind.loopKind boundary finish index s t := by
  obtain ⟨fuel, t, hRun, hReady', hCode', he⟩ :=
    register_counter kind boundary hOutside s hReady hCode hRip
  have hIncrement : (Operand.reg 15 : Operand 64).read s + 1 =
      BitVec.ofNat 64 (index + 1) := by
    rw [hIndex, BitVec.ofNat_add]
    rfl
  have hCompare : ((Operand.reg (kind.count.setWidth 5) : Operand 64).read s =
      (Operand.reg 15 : Operand 64).read s + 1) ↔ finish = index + 1 := by
    rw [hCount, hIncrement]
    constructor
    · intro hh
      have hn := congrArg BitVec.toNat hh
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (show index + 1 < 2^64 by omega)] using hn
    · intro hh
      rw [hh]
  refine ⟨t, ⟨⟨fuel, hRun⟩, hReady', hCode', ?_, ?_, ?_⟩⟩
  · have hr := he.rip
    by_cases hend : index + 1 < finish
    · have hne := mt hCompare.mp (show finish ≠ index + 1 by omega)
      have hr' : t.RIP = kind.loopPC := by
        simpa only [RegisterCounterKind.normalizedEffect, ite_eq_right hne] using hr
      cases kind <;> simpa only [RegisterCounterKind.loopPC,
        RegisterCounterKind.loopKind, LoopKind.entry, ite_eq_left hend] using hr'
    · have heq := hCompare.mpr (show finish = index + 1 by omega)
      have hr' : t.RIP = kind.finalPC := by
        simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left heq] using hr
      cases kind <;> simpa only [RegisterCounterKind.finalPC,
        RegisterCounterKind.loopKind, LoopKind.finalPC, ite_eq_right hend] using hr'
  · have hv : (Operand.reg 15 : Operand 64).read t =
        (Operand.reg 15 : Operand 64).read s + 1 := he.writes
    rw [hIncrement] at hv
    cases kind <;> exact hv
  · apply he.agrees.mono
    cases kind <;> simp [RegisterCounterKind.normalizedEffect,
      RegisterCounterKind.effect, RegisterCounterKind.loopKind, Effect.components,
      LoopKind.indexRegister]

theorem register_loop_counter [Bindings] (kind : LoopKind.Kind) (hk : kind ≠ .resetSecond)
    {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    {s : RamState} {finish index : Nat} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP ∈ kind.exits)
    (hIndex : (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s =
      BitVec.ofNat 64 index)
    (hCount : LoopKind.count kind s = BitVec.ofNat 64 finish)
    (hi : index < finish) (hb : finish < 2^64)
    (hkFinalize : kind ≠ .finalizeResetSecond := by decide)
    (hkDiscard : kind ≠ .resetDiscardSecond := by decide) :
    ∃ t, LoopCounterPost kind boundary finish index s t := by
  cases kind with
  | resetSecond => exact (hk rfl).elim
  | finalizeResetSecond => exact (hkFinalize rfl).elim
  | resetDiscardSecond => exact (hkDiscard rfl).elim
  | slices =>
    simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact register_counter_post .slicesPartial hOutside hReady hCode hRip hIndex hCount hi hb
    · exact register_counter_post .slicesFull hOutside hReady hCode hRip hIndex hCount hi hb
  | resetFirst =>
    simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact register_counter_post .resetFirstPartial hOutside hReady hCode hRip hIndex hCount hi hb
    · exact register_counter_post .resetFirstFull hOutside hReady hCode hRip hIndex hCount hi hb
  | updateFinalizeInto =>
    simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact register_counter_post .updateFinalizeIntoPartial hOutside hReady hCode hRip hIndex hCount hi hb
    · exact register_counter_post .updateFinalizeIntoFull hOutside hReady hCode hRip hIndex hCount hi hb
  | finalizeResetFirst =>
    simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact register_counter_post .finalizeResetFirstPartial hOutside hReady hCode hRip hIndex hCount hi hb
    · exact register_counter_post .finalizeResetFirstFull hOutside hReady hCode hRip hIndex hCount hi hb
  | resetDiscardFirst =>
    simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact register_counter_post .resetDiscardFirstPartial hOutside hReady hCode hRip hIndex hCount hi hb
    · exact register_counter_post .resetDiscardFirstFull hOutside hReady hCode hRip hIndex hCount hi hb

end Md5.Proofs.Streaming
