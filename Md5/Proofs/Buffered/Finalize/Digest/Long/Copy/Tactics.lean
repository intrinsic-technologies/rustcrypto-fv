import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Model
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

macro "digest_copy_load " pc:num ", " base:num ", " off:term ", " reg:term ", " src:term :
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

macro "digest_copy_store " pc:num ", " base:num ", " codeLen:term ", " off:term ", "
    reg:term ", " dst:term ", " am:term ", " len:num : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let baseOffset := Lean.quote (base.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + len.getNat - 0x100000)
  `(tactic| (
  md5_run_then (Stores.mov_m64_r64_effect_step $pc 0x48 (by unfold RexWPrefix; decide)
    $reg $am (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $pcOffset)
        (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components $pc $reg $am t)
      change RangeApart (stackPtr t + $dst) 8 $base $codeLen
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $baseOffset)
        (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))


end Md5.Proofs.Buffered.Finalize.Digest.Long.Copy
