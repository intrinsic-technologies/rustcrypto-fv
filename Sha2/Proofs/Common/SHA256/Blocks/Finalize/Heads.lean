import Sha2.Proofs.Common.SHA256.Finalize.Blocks

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

attribute [local x86_compose] stackMode Variant.buffer Variant.scratch Variant.registers
  Variant.padReg Variant.hashReg Blocks.Zero.Offset.value Blocks.Length.Registers.tail

macro "sha256_finalize_head " source:num "," destination:num "," reg:num "," last:ident
    "," pc:term "," outside:term "," inside:term : tactic => do
  let src := source.getNat + 56
  let dst := destination.getNat + 56
  let srcMode ← if src < 128 then `(AddrMode.sib 4 none 0 (.d8 $(Lean.quote src)))
    else `(AddrMode.sib 4 none 0 (.d32 $(Lean.quote src)))
  let dstMode ← if dst < 128 then `(AddrMode.sib 4 none 0 (.d8 $(Lean.quote dst)))
    else `(AddrMode.sib 4 none 0 (.d32 $(Lean.quote dst)))
  let rex := if reg.getNat < 8 then 0x48 else 0x4c
  let srcLen := if src < 128 then 5 else 8
  let dstLen := if dst < 128 then 5 else 8
  let step₁ ← if last.getId == `store then
    `(mov_m64_r64_effect_step $pc $(Lean.quote rex) (by simp [RexWPrefix])
      $(Lean.quote (reg.getNat % 8)) $srcMode (by decide) rfl rfl)
    else `(mov_r64_m64_effect_step $pc 0x48 (by simp [RexWPrefix]) 0
      $srcMode (by decide) rfl rfl)
  let step₂ ← `(mov_m64_r64_effect_step ($pc + $(Lean.quote srcLen)) $(Lean.quote rex)
    (by simp [RexWPrefix]) $(Lean.quote (reg.getNat % 8)) $dstMode (by decide) rfl rfl)
  `(tactic| (
    advance_reloc_begin $step₁
      next (boundary_ne_program $outside ($inside $(Lean.quote srcLen) (by decide)))
    advance_reloc_then $step₂
      next (boundary_ne_program $outside ($inside $(Lean.quote (srcLen + dstLen)) (by decide)))
    advance_finish [FirstHead.effect, LastHead.effect, BitVec.add_zero]))

theorem FirstHead.run [Bindings] (p : BitVec 64) (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes v).length) :
    AdvanceTriple boundary (Pre p v) (codeRange p (bytes v))
      (Effect.post (effect p v)) := by
  cases v with
  | digest => sha256_finalize_head 0, 104, 0, load, p, outside, inside
  | reset => sha256_finalize_head 0, 104, 0, load, p, outside, inside
  | finalizeFirst => sha256_finalize_head 8, 112, 0, load, p, outside, inside
  | finalizeLast => sha256_finalize_head 112, 232, 0, load, p, outside, inside
  | traitFirst => sha256_finalize_head 112, 0, 0, load, p, outside, inside
  | traitLast => sha256_finalize_head 0, 232, 0, load, p, outside, inside

theorem LastHead.run [Bindings] (p : BitVec 64) (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes v).length) :
    AdvanceTriple boundary (Pre p v) (codeRange p (bytes v))
      (Effect.post (effect p v)) := by
  cases v with
  | digest => sha256_finalize_head 0, 104, 12, store, p, outside, inside
  | reset => sha256_finalize_head 0, 104, 15, store, p, outside, inside
  | finalizeFirst => sha256_finalize_head 8, 112, 12, store, p, outside, inside
  | finalizeLast => sha256_finalize_head 112, 232, 15, store, p, outside, inside
  | traitFirst => sha256_finalize_head 112, 0, 15, store, p, outside, inside
  | traitLast => sha256_finalize_head 0, 232, 15, store, p, outside, inside

end Sha2.Proofs.Common.SHA256.Finalize
