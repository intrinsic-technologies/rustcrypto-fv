import Md5.Proofs.Buffered.Update.Counter
import Md5.Proofs.Buffered.Update.ResetFirst.KindMachine
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] fullCompressEffect

theorem fullCompressEffect_local : Effect.Local fullCompressEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [fullCompressEffect, stackPtr, h.gpr]
  · simpa only [fullCompressEffect, Effect.flag] using congrArg some hi
  · simp [fullCompressEffect, Write.Full, Operand.Full]

def batchPrepareBytes : List UInt8 :=
  [0x48, 0x01, 0x54, 0x24, 0x58] ++ fullCompressBytes

def batchPrepareEffect (s : RamState) : Effect :=
  { rip := 0x10073b
    writes := [⟨(.mem (stackPtr s + 88) : Operand 64),
      (.mem (stackPtr s + 88) : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem batch_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10072e ∧
      Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x10072e 13)
      (codeRange 0x10072e batchPrepareBytes) batchPrepareEffect := by
  have hfirst := AdvancesBlock.first
    (Update.Counter.add_m64_r64_effect_step 0x10072e 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide))
    (codeRange_mem_of_drop (p := 0x10072e) 0 (by decide +kernel))
    (P := fun s ↦ s.RIP = 0x10072e ∧ Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x10072e 13)
    (code := codeRange 0x10072e batchPrepareBytes)
    (fun s h ↦ by
      refine ⟨h.1, ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 0 5 (by decide))
    (fun s h ↦ by
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ h.2.2 rfl
      intro c hc hm
      have heq : (Update.Counter.addM64R64Effect 0x10072e
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [heq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm)
    (fun _ _ ↦ text_address_ne_return hOutside 0x733 (by decide +kernel))
  have hnext := hfirst.seq_block (full_compress_prepare boundary hOutside)
    fullCompressEffect_local
    (codeRange_mem_of_drop (p := 0x10072e) 5 (by decide +kernel))
    (by intro s _; simp [Update.Counter.addM64R64Effect, Write.Full, Operand.Full])
    (by intro s t _ he _; exact ⟨he.rip,
      Effect.Avoids.of_noMem (by simp [fullCompressEffect, Effect.components, Component.Covers]) _⟩)
  refine AdvancesBlock.block_end ?_ hnext
  intro s t _ he
  apply he.weaken
  · x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro i; cases i <;> x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    rfl

end Md5.Proofs.Buffered.ResetFirst

namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] fullCompressEffect

theorem fullCompressEffect_local : Effect.Local fullCompressEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [fullCompressEffect, stackPtr, h.gpr]
  · simpa only [fullCompressEffect, Effect.flag] using congrArg some hi
  · simp [fullCompressEffect, Write.Full, Operand.Full]

def batchPrepareBytes : List UInt8 :=
  [0x48, 0x01, 0x54, 0x24, 0x58] ++ fullCompressBytes

def batchPrepareEffect (s : RamState) : Effect :=
  { rip := 0x100deb
    writes := [⟨(.mem (stackPtr s + 88) : Operand 64),
      (.mem (stackPtr s + 88) : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem batch_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100dde ∧
      Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x100dde 13)
      (codeRange 0x100dde batchPrepareBytes) batchPrepareEffect := by
  have hfirst := AdvancesBlock.first
    (Update.Counter.add_m64_r64_effect_step 0x100dde 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide))
    (codeRange_mem_of_drop (p := 0x100dde) 0 (by decide +kernel))
    (P := fun s ↦ s.RIP = 0x100dde ∧ Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x100dde 13)
    (code := codeRange 0x100dde batchPrepareBytes)
    (fun s h ↦ by
      refine ⟨h.1, ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 0 5 (by decide))
    (fun s h ↦ by
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ h.2.2 rfl
      intro c hc hm
      have heq : (Update.Counter.addM64R64Effect 0x100dde
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [heq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm)
    (fun _ _ ↦ text_address_ne_return hOutside 0xde3 (by decide +kernel))
  have hnext := hfirst.seq_block (full_compress_prepare boundary hOutside)
    fullCompressEffect_local
    (codeRange_mem_of_drop (p := 0x100dde) 5 (by decide +kernel))
    (by intro s _; simp [Update.Counter.addM64R64Effect, Write.Full, Operand.Full])
    (by intro s t _ he _; exact ⟨he.rip,
      Effect.Avoids.of_noMem (by simp [fullCompressEffect, Effect.components, Component.Covers]) _⟩)
  refine AdvancesBlock.block_end ?_ hnext
  intro s t _ he
  apply he.weaken
  · x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro i; cases i <;> x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    rfl

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

namespace Md5.Proofs.Buffered.ResetFirst.ResetDiscardFirst

open X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect

theorem fullCompressEffect_local : Effect.Local Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect, stackPtr, h.gpr]
  · simpa only [Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect, Effect.flag] using congrArg some hi
  · simp [Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect, Write.Full, Operand.Full]

def batchPrepareBytes : List UInt8 :=
  [0x48, 0x01, 0x54, 0x24, 0x70] ++ Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressBytes

def batchPrepareEffect (s : RamState) : Effect :=
  { rip := 0x101474
    writes := [⟨(.mem (stackPtr s + 112) : Operand 64),
      (.mem (stackPtr s + 112) : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 96⟩,
      ⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem batch_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101467 ∧
      Memory.MemWritable s (stackPtr s + 112) 8 ∧
      RangeApart (stackPtr s + 112) 8 0x101467 13)
      (codeRange 0x101467 batchPrepareBytes) batchPrepareEffect := by
  have hfirst := AdvancesBlock.first
    (Update.Counter.add_m64_r64_effect_step 0x101467 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide))
    (codeRange_mem_of_drop (p := 0x101467) 0 (by decide +kernel))
    (P := fun s ↦ s.RIP = 0x101467 ∧ Memory.MemWritable s (stackPtr s + 112) 8 ∧
      RangeApart (stackPtr s + 112) 8 0x101467 13)
    (code := codeRange 0x101467 batchPrepareBytes)
    (fun s h ↦ by
      refine ⟨h.1, ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 0 5 (by decide))
    (fun s h ↦ by
      apply Effect.avoids_of_mem (addr := stackPtr s + 112) (len := 8) ?_ h.2.2 rfl
      intro c hc hm
      have heq : (Update.Counter.addM64R64Effect 0x101467
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 112)) s).components =
          [.mem (stackPtr s + 112) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [heq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm)
    (fun _ _ ↦ text_address_ne_return hOutside 0x146c (by decide +kernel))
  have hnext := hfirst.seq_block (Md5.Proofs.NewEntries.Reset.FirstUpdate.full_compress_prepare boundary hOutside)
    fullCompressEffect_local
    (codeRange_mem_of_drop (p := 0x101467) 5 (by decide +kernel))
    (by intro s _; simp [Update.Counter.addM64R64Effect, Write.Full, Operand.Full])
    (by intro s t _ he _; exact ⟨he.rip,
      Effect.Avoids.of_noMem (by simp [Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressEffect, Effect.components, Component.Covers]) _⟩)
  refine AdvancesBlock.block_end ?_ hnext
  intro s t _ he
  apply he.weaken
  · x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro i; cases i <;> x86_norm [batchPrepareEffect]
  · x86_norm [batchPrepareEffect, stackPtr]
    rfl

end Md5.Proofs.Buffered.ResetFirst.ResetDiscardFirst
namespace Md5.Proofs.Buffered.ResetFirst
open X86 X86.Machine X86.UserProcess X86Proofs Block

def batchPrepareBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then ResetDiscardFirst.batchPrepareBytes else batchPrepareBytes

def batchPrepareEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x73b
    writes := [⟨(.mem (stackPtr s + stackOffset kind 88) : Operand 64),
      (.mem (stackPtr s + stackOffset kind 88) : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem batch_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x72e ∧
      Memory.MemWritable s (stackPtr s + stackOffset kind 88) 8 ∧
      RangeApart (stackPtr s + stackOffset kind 88) 8 (pc kind 0x72e) 13)
      (codeRange (pc kind 0x72e) (batchPrepareBytes_of_kind kind)) (batchPrepareEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact batch_prepare boundary hOutside
  · exact FinalizeResetFirst.batch_prepare boundary hOutside
  · exact ResetDiscardFirst.batch_prepare boundary hOutside
end Md5.Proofs.Buffered.ResetFirst
