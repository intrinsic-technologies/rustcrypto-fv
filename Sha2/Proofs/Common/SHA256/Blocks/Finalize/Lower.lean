import Sha2.Proofs.Common.SHA256.Finalize.Blocks

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

attribute [local x86_compose] stackMode Variant.buffer Variant.scratch Blocks.Zero.Offset.value

macro "sha256_finalize_lower " source:num "," destination:num
    "," pc:term "," outside:term "," inside:term : tactic => do
  let mut pos := 0
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  let instructions := ([48,40,32,24,16] : List Nat).flatMap (fun i =>
    [(true, 0, i), (false, 0, i)]) ++ [(true, 0, 0), (true, 1, 8), (false, 1, 8), (false, 0, 0)]
  for (load, reg, i) in instructions do
    let n := (if load then source.getNat else destination.getNat) + i
    let am ← if n = 0 then `(AddrMode.sib 4 none 0 .none)
      else if n < 128 then `(AddrMode.sib 4 none 0 (.d8 $(Lean.quote n)))
      else `(AddrMode.sib 4 none 0 (.d32 $(Lean.quote n)))
    let addr ← if pos = 0 then pure pc else `($pc + $(Lean.quote pos))
    let step ← if load then `(mov_r64_m64_effect_step $addr 0x48 (by simp [RexWPrefix])
      $(Lean.quote reg) $am (by decide) rfl rfl)
      else `(mov_m64_r64_effect_step $addr 0x48 (by simp [RexWPrefix])
        $(Lean.quote reg) $am (by decide) rfl rfl)
    let first := pos = 0
    pos := pos + (if n = 0 then 4 else if n < 128 then 5 else 8)
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn))
  let mut result ← `(tactic| advance_finish [Lower.effect, BitVec.add_zero])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

set_option maxHeartbeats 2000000 in
theorem Lower.run [Bindings] (p : BitVec 64) (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes v).length) :
    AdvanceTriple boundary (Pre p v) (codeRange p (bytes v))
      (Effect.post (effect p v)) := by
  cases v with
  | digest => sha256_finalize_lower 0, 104, p, outside, inside
  | reset => sha256_finalize_lower 0, 104, p, outside, inside
  | finalizeFirst => sha256_finalize_lower 8, 112, p, outside, inside
  | finalizeLast => sha256_finalize_lower 112, 232, p, outside, inside
  | traitFirst => sha256_finalize_lower 112, 0, p, outside, inside
  | traitLast => sha256_finalize_lower 0, 232, p, outside, inside

end Sha2.Proofs.Common.SHA256.Finalize
