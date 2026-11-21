import Md5.Proofs.Streaming.Control

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

inductive CounterJumpKind where
  | slices
  | resetFirst
  | resetSecond
  | updateFinalizeInto
  | finalizeResetFirst
  | finalizeResetSecond
  | resetDiscardFirst
  | resetDiscardSecond

namespace CounterJumpKind

def entry : CounterJumpKind → BitVec 64
  | .slices => 0x10041b
  | .resetFirst => 0x100777
  | .resetSecond => 0x100a80
  | .updateFinalizeInto => 0x1019cb
  | .finalizeResetFirst => 0x100e27
  | .finalizeResetSecond => 0x101110
  | .resetDiscardFirst => 0x1014b2
  | .resetDiscardSecond => 0x1015ed

def displacement : CounterJumpKind → BitVec 8
  | .slices | .resetSecond => 14
  | .resetFirst => 23
  | .updateFinalizeInto => 14
  | .finalizeResetFirst => 23
  | .finalizeResetSecond => 14
  | .resetDiscardFirst => 19
  | .resetDiscardSecond => 14

def target : CounterJumpKind → BitVec 64
  | .slices => 0x10042b
  | .resetFirst => 0x100790
  | .resetSecond => 0x100a90
  | .updateFinalizeInto => 0x1019db
  | .finalizeResetFirst => 0x100e40
  | .finalizeResetSecond => 0x101120
  | .resetDiscardFirst => 0x1014c7
  | .resetDiscardSecond => 0x1015fd

end CounterJumpKind

theorem counter_finish_jump [Bindings] (kind : CounterJumpKind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = kind.entry) Extracted.programImage
      (fun _ ↦ { rip := kind.target }) := by
  intro s hReady hCode hRip
  have hBytes : CodeIn (codeRange kind.entry (0xeb :: immBytes 8 kind.displacement)) s := by
    cases kind
    · exact program_text_slice hCode 0x41b 2 (by decide +kernel)
    · exact program_text_slice hCode 0x777 2 (by decide +kernel)
    · exact program_text_slice hCode 0xa80 2 (by decide +kernel)
    · exact program_text_slice hCode 0x19cb 2 (by decide +kernel)
    · exact program_text_slice hCode 0xe27 2 (by decide +kernel)
    · exact program_text_slice hCode 0x1110 2 (by decide +kernel)
    · exact program_text_slice hCode 0x14b2 2 (by decide +kernel)
    · exact program_text_slice hCode 0x15ed 2 (by decide +kernel)
  have hTarget : branchTarget kind.entry 2 (kind.displacement.signExtend 64) = kind.target := by
    cases kind <;> decide +kernel
  have hBoundary : kind.target ≠ boundary.rip := by
    cases kind
    · exact text_address_ne_return hOutside 0x42b (by decide +kernel)
    · exact text_address_ne_return hOutside 0x790 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xa90 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x19db (by decide +kernel)
    · exact text_address_ne_return hOutside 0xe40 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1120 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x14c7 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x15fd (by decide +kernel)
  obtain ⟨t, hRun, hReady', hEffect⟩ :=
    (jmp_rel8_effect_step kind.entry kind.displacement (by
      rw [hTarget]; cases kind <;> decide +kernel)).advances hReady hBytes hRip
        (by simpa only [jmpEffect, hTarget] using hBoundary)
  refine ⟨1, t, hRun, hReady', hEffect.agrees.codeIn (by simp [Component.Covers]) hCode, ?_⟩
  simpa only [jmpEffect, hTarget] using hEffect

def RegisterCounterKind.finalPC : RegisterCounterKind → BitVec 64
  | .slicesPartial | .slicesFull => 0x10042b
  | .resetFirstPartial | .resetFirstFull => 0x100790

  | .updateFinalizeIntoPartial | .updateFinalizeIntoFull => 0x1019db
  | .finalizeResetFirstPartial | .finalizeResetFirstFull => 0x100e40
  | .resetDiscardFirstPartial | .resetDiscardFirstFull => 0x1014c7
def RegisterCounterKind.normalizedEffect (kind : RegisterCounterKind) (s : RamState) : Effect :=
  { kind.effect s with rip :=
      if (Operand.reg (kind.count.setWidth 5) : Operand 64).read s =
        (Operand.reg 15 : Operand 64).read s + 1 then kind.finalPC else kind.loopPC }

theorem register_counter [Bindings] (kind : RegisterCounterKind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = kind.pc) Extracted.programImage
      kind.normalizedEffect := by
  intro s hReady hCode hRip
  obtain ⟨fuel, u, hRun, hReady', hCode', hEffect⟩ :=
    register_counter_branch kind boundary hOutside s hReady hCode hRip
  by_cases hEq : (Operand.reg (kind.count.setWidth 5) : Operand 64).read s =
      (Operand.reg 15 : Operand 64).read s + 1
  · cases kind with
    | slicesPartial =>
      exact ⟨fuel, u, hRun, hReady', hCode', hEffect⟩
    | resetFirstPartial =>
      exact ⟨fuel, u, hRun, hReady', hCode', hEffect⟩
    | slicesFull =>
      have hu : u.RIP = CounterJumpKind.slices.entry := by
        simpa only [RegisterCounterKind.effect, ite_eq_left hEq, RegisterCounterKind.donePC, CounterJumpKind.entry]
          using hEffect.rip
      obtain ⟨steps, t, hRun', hReady'', hCode'', hJump⟩ :=
        counter_finish_jump .slices boundary hOutside u hReady' hCode' hu
      refine ⟨fuel + steps, t, hRun.trans hRun', hReady'', hCode'', ?_, ?_, by trivial, ?_⟩
      · simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left hEq,
          RegisterCounterKind.finalPC, CounterJumpKind.target] using hJump.rip
      · exact (hJump.agrees.read (n := 64) (r := 15) (by simp [Effect.components])).trans
          (show (Operand.reg 15 : Operand 64).read u = _ from hEffect.writes)
      · apply (hEffect.agrees.trans hJump.agrees).mono
        simp [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect, Effect.components]
    | resetFirstFull =>
      have hu : u.RIP = CounterJumpKind.resetFirst.entry := by
        simpa only [RegisterCounterKind.effect, ite_eq_left hEq, RegisterCounterKind.donePC, CounterJumpKind.entry]
          using hEffect.rip
      obtain ⟨steps, t, hRun', hReady'', hCode'', hJump⟩ :=
        counter_finish_jump .resetFirst boundary hOutside u hReady' hCode' hu
      refine ⟨fuel + steps, t, hRun.trans hRun', hReady'', hCode'', ?_, ?_, by trivial, ?_⟩
      · simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left hEq,
          RegisterCounterKind.finalPC, CounterJumpKind.target] using hJump.rip
      · exact (hJump.agrees.read (n := 64) (r := 15) (by simp [Effect.components])).trans
          (show (Operand.reg 15 : Operand 64).read u = _ from hEffect.writes)
      · apply (hEffect.agrees.trans hJump.agrees).mono
        simp [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect, Effect.components]
    | updateFinalizeIntoPartial =>
      exact ⟨fuel, u, hRun, hReady', hCode', hEffect⟩
    | updateFinalizeIntoFull =>
      have hu : u.RIP = CounterJumpKind.updateFinalizeInto.entry := by
        simpa only [RegisterCounterKind.effect, ite_eq_left hEq, RegisterCounterKind.donePC, CounterJumpKind.entry]
          using hEffect.rip
      obtain ⟨steps, t, hRun', hReady'', hCode'', hJump⟩ :=
        counter_finish_jump .updateFinalizeInto boundary hOutside u hReady' hCode' hu
      refine ⟨fuel + steps, t, hRun.trans hRun', hReady'', hCode'', ?_, ?_, by trivial, ?_⟩
      · simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left hEq,
          RegisterCounterKind.finalPC, CounterJumpKind.target] using hJump.rip
      · exact (hJump.agrees.read (n := 64) (r := 15) (by simp [Effect.components])).trans
          (show (Operand.reg 15 : Operand 64).read u = _ from hEffect.writes)
      · apply (hEffect.agrees.trans hJump.agrees).mono
        simp [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect, Effect.components]
    | finalizeResetFirstPartial =>
      exact ⟨fuel, u, hRun, hReady', hCode', hEffect⟩
    | finalizeResetFirstFull =>
      have hu : u.RIP = CounterJumpKind.finalizeResetFirst.entry := by
        simpa only [RegisterCounterKind.effect, ite_eq_left hEq, RegisterCounterKind.donePC, CounterJumpKind.entry]
          using hEffect.rip
      obtain ⟨steps, t, hRun', hReady'', hCode'', hJump⟩ :=
        counter_finish_jump .finalizeResetFirst boundary hOutside u hReady' hCode' hu
      refine ⟨fuel + steps, t, hRun.trans hRun', hReady'', hCode'', ?_, ?_, by trivial, ?_⟩
      · simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left hEq,
          RegisterCounterKind.finalPC, CounterJumpKind.target] using hJump.rip
      · exact (hJump.agrees.read (n := 64) (r := 15) (by simp [Effect.components])).trans
          (show (Operand.reg 15 : Operand 64).read u = _ from hEffect.writes)
      · apply (hEffect.agrees.trans hJump.agrees).mono
        simp [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect, Effect.components]
    | resetDiscardFirstPartial =>
      exact ⟨fuel, u, hRun, hReady', hCode', hEffect⟩
    | resetDiscardFirstFull =>
      have hu : u.RIP = CounterJumpKind.resetDiscardFirst.entry := by
        simpa only [RegisterCounterKind.effect, ite_eq_left hEq, RegisterCounterKind.donePC, CounterJumpKind.entry]
          using hEffect.rip
      obtain ⟨steps, t, hRun', hReady'', hCode'', hJump⟩ :=
        counter_finish_jump .resetDiscardFirst boundary hOutside u hReady' hCode' hu
      refine ⟨fuel + steps, t, hRun.trans hRun', hReady'', hCode'', ?_, ?_, by trivial, ?_⟩
      · simpa only [RegisterCounterKind.normalizedEffect, ite_eq_left hEq,
          RegisterCounterKind.finalPC, CounterJumpKind.target] using hJump.rip
      · exact (hJump.agrees.read (n := 64) (r := 15) (by simp [Effect.components])).trans
          (show (Operand.reg 15 : Operand 64).read u = _ from hEffect.writes)
      · apply (hEffect.agrees.trans hJump.agrees).mono
        simp [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect, Effect.components]
  · refine ⟨fuel, u, hRun, hReady', hCode', ?_⟩
    simpa only [RegisterCounterKind.normalizedEffect, RegisterCounterKind.effect,
      ite_eq_right hEq] using hEffect

end Md5.Proofs.Streaming
