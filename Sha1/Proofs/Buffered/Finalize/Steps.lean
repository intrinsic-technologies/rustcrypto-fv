import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple

namespace Sha1.Proofs.Buffered.Finalize.Steps

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

structure PartPre (kind : Kind) (entry : BitVec 64) (s : RamState) : Prop
    extends Storage kind s where
  rip : s.RIP = entry

macro "storage_copy_load " _kind:term ", " pc:num ", " base:num ", " off:term ", " reg:term ", " src:term :
    tactic => do
  let nextOffset := Lean.quote (pc.getNat + 5 - 0x100000)
  `(tactic| (
  md5_run_then (mov_r64_m64_effect_step $pc 0x48 (by unfold RexWPrefix; decide)
    $reg (.sib 4 none 0 (.d8 $src)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable $src 8 (by decide)).readable
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

macro "storage_copy_store " _kind:term ", " pc:num ", " base:num ", " codeLen:term ", " off:term ", "
    rex:term ", " reg:term ", " dst:term ", " am:term ", " len:num : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let baseOffset := Lean.quote (base.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + len.getNat - 0x100000)
  `(tactic| (
  md5_run_then (Common.Instructions.MovStore.mov_m64_r64_effect_step $pc $rex
    (by unfold RexWPrefix; decide) $reg $am (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $pcOffset) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + $dst) 8 $base $codeLen
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $baseOffset) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

macro "storage_copy_store32 " _kind:term ", " pc:num ", " base:num ", " codeLen:term ", " off:term ", "
    rex:term ", " reg:term ", " dst:term ", " am:term ", " len:num : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let baseOffset := Lean.quote (base.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + len.getNat - 0x100000)
  `(tactic| (
  md5_run_then (Common.Instructions.MovStore.mov_m32_r32_effect_step $pc $rex
    (by unfold RexNoWPrefix; decide) $reg $am (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 4 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 4)
        (codeOffset := $pcOffset) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM32R32Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + $dst) 4 $base $codeLen
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 4)
        (codeOffset := $baseOffset) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

macro "steps_copy_load " pc:num ", " base:num ", " off:term ", " reg:term ", " src:term :
    tactic => do
  let nextOffset := Lean.quote (pc.getNat + 5 - 0x100000)
  `(tactic| (
  md5_run_then (mov_r64_m64_effect_step $pc 0x48 (by unfold RexWPrefix; decide)
    $reg (.sib 4 none 0 (.d8 $src)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable $src 8 (by decide)).readable
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

macro "steps_copy_store " pc:num ", " base:num ", " codeLen:term ", " off:term ", "
    rex:term ", " reg:term ", " dst:term ", " am:term ", " len:num : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let baseOffset := Lean.quote (base.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + len.getNat - 0x100000)
  `(tactic| (
  md5_run_then (Common.Instructions.MovStore.mov_m64_r64_effect_step $pc $rex
    (by unfold RexWPrefix; decide) $reg $am (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $pcOffset) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + $dst) 8 $base $codeLen
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $baseOffset) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

end Sha1.Proofs.Buffered.Finalize.Steps
