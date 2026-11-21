import Sha2.Proofs.Common.SHA256.Finalize.Blocks
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

attribute [local x86_compose] stackMode Variant.scratch Variant.hashReg

macro "sha256_finalize_setup " scratch:num "," hash:num "," special:ident "," last:ident
    "," pc:term "," outside:term "," inside:term : tactic => do
  let mode (n : Nat) : Lean.MacroM (Lean.TSyntax `term) :=
    if n = 0 then `(AddrMode.sib 4 none 0 .none)
    else if n < 128 then `(AddrMode.sib 4 none 0 (.d8 $(Lean.quote n)))
    else `(AddrMode.sib 4 none 0 (.d32 $(Lean.quote n)))
  let mut pos := 0
  let mut instructions : Array (Lean.TSyntax `term × Nat) := #[]
  if special.getId == `trait then
    instructions := instructions.push (← `(mov_r64_r64_effect_step $pc 0x48 0xe6
      (by simp [RexWPrefix]) rfl), 3)
  else
    let am ← mode scratch.getNat
    instructions := instructions.push (← `(lea_r64_effect_step $pc 0x48
      (by simp [RexWPrefix]) 6 $am (by decide) rfl rfl),
      if scratch.getNat = 0 then 4 else if scratch.getNat < 128 then 5 else 8)
  pos := instructions[0]!.2
  instructions := instructions.push (← `(mov_r32_imm32_effect_step
    ($pc + $(Lean.quote pos)) 0xba (by decide) 1), 5)
  pos := pos + 5
  if special.getId == `finalize then
    let am ← mode 72
    let reg := if last.getId == `yes then 3 else 7
    instructions := instructions.push (← `(lea_r64_effect_step ($pc + $(Lean.quote pos))
      0x48 (by simp [RexWPrefix]) $(Lean.quote reg) $am (by decide) rfl rfl), 5)
    pos := pos + 5
  if special.getId != `finalize || last.getId == `yes then
    let rex := if hash.getNat < 8 then 0x48 else 0x4c
    let modrm := 0xc0 + (hash.getNat % 8) * 8 + 7
    instructions := instructions.push (← `(mov_r64_r64_effect_step ($pc + $(Lean.quote pos))
      $(Lean.quote rex) $(Lean.quote modrm) (by simp [RexWPrefix]) rfl), 3)
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  pos := 0
  for (step, len) in instructions do
    let first := pos = 0
    pos := pos + len
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn))
  let mut result ← `(tactic| advance_finish [Setup.effect, BitVec.add_zero])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

theorem Setup.run [Bindings] (p : BitVec 64) (v : Variant) (last : Bool)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (bytes v last).length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (bytes v last))
      (Effect.post (effect p v last)) := by
  cases v with
  | digest => cases last <;> sha256_finalize_setup 104, 14, normal, no, p, outside, inside
  | reset => cases last <;> sha256_finalize_setup 104, 3, normal, no, p, outside, inside
  | finalizeFirst =>
    cases last with
    | false => sha256_finalize_setup 112, 3, finalize, no, p, outside, inside
    | true => sha256_finalize_setup 112, 3, finalize, yes, p, outside, inside
  | finalizeLast => cases last <;> sha256_finalize_setup 232, 3, normal, no, p, outside, inside
  | traitFirst => cases last <;> sha256_finalize_setup 0, 5, trait, no, p, outside, inside
  | traitLast => cases last <;> sha256_finalize_setup 232, 3, normal, no, p, outside, inside

end Sha2.Proofs.Common.SHA256.Finalize
