import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts
import Md5.Proofs.Buffered.FinalizeReset.Length.Register
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block
open Md5.Proofs.Buffered.FinalizeReset.Length

def bytes (variant : Variant := .original) : List UInt8 :=
  [0x41, 0xc1, 0xe7, 3, 0x49, 0xc1, 0xe6, 9, 0x4d, 0x09, 0xfe,
    0x4c, 0x89, 0xb4, 0x24, UInt8.ofNat (variant.tailOffset + 56), 0, 0, 0,
    0x4c, 0x89, 0xb4, 0x24, UInt8.ofNat (variant.blockOffset + 56), 1, 0, 0]

structure RunPre (s : RamState) (variant : Variant := .original) : Prop extends Storage variant.toKind s where
  rip : s.RIP = variant.paddedRip

def positionValue (s : RamState) : BitVec 64 :=
  (((Operand.reg 15 : Operand 32).read s) <<< 3).setWidth 64

def value (s : RamState) : BitVec 64 :=
  ((Operand.reg 14 : Operand 64).read s <<< 9) ||| positionValue s

def effect (s : RamState) (variant : Variant := .original) : Effect :=
  { rip := variant.paddedRip + 27
    writes := [⟨(.reg 15 : Operand 64), positionValue s⟩,
      ⟨(.reg 14 : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 56)) : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.blockOffset + 56)) : Operand 64), value s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

local macro "reset_length_execution" outside:ident p0:num p4:num p8:num p11:num p19:num _p27:num o4:num o8:num o11:num o19:num o27:num o0:num a:num b:num : tactic =>
  `(tactic| (
  unfold bytes
  md5_run_begin (shl_r32_imm8_rex_effect_step $p0 0x41 0xe7 3
    (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return $outside $o4 (by decide +kernel)
  md5_run_then (shl_r64_imm8_effect_step $p4 0x49 0xe6 9
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $p0) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return $outside $o8 (by decide +kernel)
  md5_run_then (or_r64_r64_effect_step $p8 0x4d 0xfe
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $p0) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return $outside $o11 (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step $p11 0x4c
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 $a))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $p0) 11 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $a 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $a) (len := 8)
        (codeOffset := $o11)
        (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components $p11 14 (.sib 4 none 0 (.d32 $a)) t)
      change RangeApart (stackPtr t + $a) 8 $p0 27
      rw [hsp]
      exact h.toStorage.stackApart (offset := $a) (len := 8)
        (codeOffset := $o0) (codeLen := 27)
        (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return $outside $o19 (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step $p19 0x4c
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 $b))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $p0) 19 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $b 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $b) (len := 8)
        (codeOffset := $o19)
        (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components $p19 14 (.sib 4 none 0 (.d32 $b)) t)
      change RangeApart (stackPtr t + $b) 8 $p0 27
      rw [hsp]
      exact h.toStorage.stackApart (offset := $b) (len := 8)
        (codeOffset := $o0) (codeLen := 27)
        (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return $outside $o27 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [Variant.paddedRip, Variant.tailOffset, Variant.blockOffset, effect]
  · x86_norm [Variant.paddedRip, Variant.tailOffset, Variant.blockOffset, effect, value, positionValue, stackPtr]
    exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · intro i; cases i <;> x86_norm [Variant.paddedRip, Variant.tailOffset, Variant.blockOffset, effect]
  · x86_norm [Variant.paddedRip, Variant.tailOffset, Variant.blockOffset, effect, stackPtr]
    exact ⟨Or.inl rfl, Or.inr rfl⟩

  ))

set_option maxHeartbeats 800000 in
theorem execution [Bindings] {variant : Variant} (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ RunPre s variant) (codeRange variant.paddedRip (bytes variant)) (fun s ↦ effect s variant) := by
  cases variant
  · reset_length_execution hOutside 0x100bcf 0x100bd3 0x100bd7 0x100bda 0x100be2 0x100bea 0xbd3 0xbd7 0xbda 0xbe2 0xbea 0xbcf 0x98 0x120
  · reset_length_execution hOutside 0x10125f 0x101263 0x101267 0x10126a 0x101272 0x10127a 0x1263 0x1267 0x126a 0x1272 0x127a 0x125f 0x98 0x120
  · reset_length_execution hOutside 0x101757 0x10175b 0x10175f 0x101762 0x10176a 0x101772 0x175b 0x175f 0x1762 0x176a 0x1772 0x1757 0xc0 0x118

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length
