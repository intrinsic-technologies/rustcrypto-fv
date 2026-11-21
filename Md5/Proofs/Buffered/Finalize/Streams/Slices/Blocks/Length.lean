import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.FinalizeReset.Length.Register
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block
open Md5.Proofs.Buffered.FinalizeReset.Length

def bytes : List UInt8 :=
  [0x41, 0xc1, 0xe7, 3, 0x49, 0xc1, 0xe6, 9, 0x4d, 0x09, 0xfe,
    0x4c, 0x89, 0x74, 0x24, 0x48,
    0x4c, 0x89, 0xb4, 0x24, 0xa0, 0, 0, 0]

structure RunPre (s : RamState) (update : Bool := false) : Prop extends Storage (streamKind update) s where
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x10053d))

def positionValue (s : RamState) : BitVec 64 :=
  (((Operand.reg 15 : Operand 32).read s) <<< 3).setWidth 64

def value (s : RamState) : BitVec 64 :=
  ((Operand.reg 14 : Operand 64).read s <<< 9) ||| positionValue s

def effect (s : RamState) (update : Bool := false) : Effect :=
  { rip := (BitVec.ofNat 64 (relocated update 0x100555))
    writes := [⟨(.reg 15 : Operand 64), positionValue s⟩,
      ⟨(.reg 14 : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 160) : Operand 64), value s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem execution {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (RunPre (update := update)) (codeRange (BitVec.ofNat 64 (relocated update 0x10053d)) bytes) (effect (update := update)) := by
  cases update with
  | false =>
    unfold bytes
    md5_run_begin (shl_r32_imm8_rex_effect_step 0x10053d 0x41 0xe7 3
      (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x541 (by decide +kernel)
    md5_run_then (shl_r64_imm8_effect_step 0x100541 0x49 0xe6 9
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x10053d) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x545 (by decide +kernel)
    md5_run_then (or_r64_r64_effect_step 0x100545 0x4d 0xfe
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x10053d) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x548 (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x100548 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 72))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x10053d) 11 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 72 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 72) (len := 8)
          (codeOffset := 0x548) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x100548 14 (.sib 4 none 0 (.d8 72)) t)
        change RangeApart (stackPtr t + 72) 8 0x10053d 24
        rw [hsp]
        exact h.toStorage.stackApart (offset := 72) (len := 8)
          (codeOffset := 0x53d) (codeLen := 24) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x54d (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x10054d 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 160))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x10053d) 16 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 160 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 160) (len := 8)
          (codeOffset := 0x54d) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x10054d 14 (.sib 4 none 0 (.d32 160)) t)
        change RangeApart (stackPtr t + 160) 8 0x10053d 24
        rw [hsp]
        exact h.toStorage.stackApart (offset := 160) (len := 8)
          (codeOffset := 0x53d) (codeLen := 24) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x555 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, value, positionValue, stackPtr]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      exact ⟨Or.inl rfl, Or.inr rfl⟩
  | true =>
    unfold bytes
    md5_run_begin (shl_r32_imm8_rex_effect_step 0x101aed 0x41 0xe7 3
      (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1af1 (by decide +kernel)
    md5_run_then (shl_r64_imm8_effect_step 0x101af1 0x49 0xe6 9
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101aed) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1af5 (by decide +kernel)
    md5_run_then (or_r64_r64_effect_step 0x101af5 0x4d 0xfe
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101aed) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1af8 (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x101af8 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 72))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101aed) 11 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 72 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 72) (len := 8)
          (codeOffset := 0x1af8) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x101af8 14 (.sib 4 none 0 (.d8 72)) t)
        change RangeApart (stackPtr t + 72) 8 0x101aed 24
        rw [hsp]
        exact h.toStorage.stackApart (offset := 72) (len := 8)
          (codeOffset := 0x1aed) (codeLen := 24) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1afd (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x101afd 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 160))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101aed) 16 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 160 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 160) (len := 8)
          (codeOffset := 0x1afd) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x101afd 14 (.sib 4 none 0 (.d32 160)) t)
        change RangeApart (stackPtr t + 160) 8 0x101aed 24
        rw [hsp]
        exact h.toStorage.stackApart (offset := 160) (len := 8)
          (codeOffset := 0x1aed) (codeLen := 24) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b05 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, value, positionValue, stackPtr]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      exact ⟨Or.inl rfl, Or.inr rfl⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length
