import Sha2.Proofs.Common.SHA256.Finalize.Blocks
import Sha2.Proofs.Wrapper.Hash.Padding.FillSetup
import Sha2.Proofs.Common.Instructions.XorImmediate

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate

attribute [local x86_compose] Variant.buffer Variant.registers Variant.padReg
  Blocks.Zero.Offset.value Blocks.Length.Registers.tail Mark.address movM8Imm8RexEffect
  incR64Effect BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero
attribute [local x86_local] Sha2.Proofs.Wrapper.Hash.Padding.FillSetup.byteStore_local
  Sha2.Proofs.Wrapper.Hash.Padding.FillSetup.increment_local

@[local x86_compose] theorem literal_add_register (n : Nat) (r : BitVec 5) (s : RamState) :
    BitVec.ofNat 64 n + (.reg r : Operand 64).read s =
      (.reg r : Operand 64).read s + BitVec.ofNat 64 n := BitVec.add_comm _ _

@[local x86_compose] theorem literal_add_register_add (n : Nat) (r : BitVec 5)
    (s : RamState) (offset : BitVec 64) :
    BitVec.ofNat 64 n + ((.reg r : Operand 64).read s + offset) =
      (.reg r : Operand 64).read s + (BitVec.ofNat 64 n + offset) :=
  by rw [← BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n), BitVec.add_assoc]

macro "sha256_finalize_mark " buffer:num "," tail:num "," pad:num
    "," pc:term "," outside:term "," inside:term : tactic => do
  let tr := tail.getNat
  let pr := pad.getNat
  let rex := 0x48 + (if tr < 8 then 0 else 4) + (if pr < 8 then 0 else 1)
  let modrm := 0xc0 + (tr % 8) * 8 + pr % 8
  let xorRex := if pr < 8 then 0x48 else 0x49
  let xorModrm := 0xf0 + pr % 8
  let buf := buffer.getNat
  let mut ins : Array (Lean.TSyntax `term × Nat) := #[]
  ins := ins.push (← `(show StepEffect _ _
    (movR64R64Effect $pc $(Lean.quote pr) $(Lean.quote tr)) from
      mov_r64_r64_effect_step $pc $(Lean.quote rex) $(Lean.quote modrm)
        (by simp [RexWPrefix]) rfl), 3)
  ins := ins.push (← `(StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR64Imm8Effect ($pc + 3) $(Lean.quote pr) 63) from
      xor_r64_imm8_effect_step ($pc + 3) $(Lean.quote xorRex) $(Lean.quote xorModrm) 63
        (by simp [RexWPrefix]) rfl rfl))), 4)
  let am ← if buf = 0 then `(AddrMode.sib 4 (some $(Lean.quote tr)) 0 .none)
    else `(AddrMode.sib 4 (some $(Lean.quote tr)) 0 (.d8 $(Lean.quote buf)))
  ins := ins.push (← `(mov_m8_imm8_rex_effect_step ($pc + 7) 0x42
    (by simp [RexNoWPrefix, RexPrefix]) $am (by decide) rfl rfl 128), if buf = 0 then 5 else 6)
  let mut pos := 7 + (if buf = 0 then 5 else 6)
  ins := ins.push (← `(lea_r64_effect_step ($pc + $(Lean.quote pos)) 0x4a
    (by simp [RexWPrefix]) 7 (.sib 4 (some $(Lean.quote tr)) 0 .none)
    (by decide) rfl rfl), 4)
  pos := pos + 4
  if buf = 0 then
    ins := ins.push (← `(StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (incR64Effect ($pc + $(Lean.quote pos)) 7) from
        inc_r64_effect_step ($pc + $(Lean.quote pos)) 0x48 0xc7
          (by simp [RexWPrefix]) rfl rfl))), 3)
    pos := pos + 3
  else
    ins := ins.push (← `(StepEffect.forgetFlags (h :=
      (show StepEffect _ _
        (addR64Imm8Effect ($pc + $(Lean.quote pos)) 7 $(Lean.quote (buf + 1))) from
        add_r64_imm8_effect_step ($pc + $(Lean.quote pos)) 0x48 0xc7 $(Lean.quote (buf + 1))
          (by simp [RexWPrefix]) rfl rfl))), 4)
    pos := pos + 4
  ins := ins.push (← `(StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect ($pc + $(Lean.quote pos)) 2 6 6) from
      xor_r32_r32_effect_step ($pc + $(Lean.quote pos)) 0xf6 rfl))), 2)
  pos := pos + 2
  let movRex := if pr < 8 then 0x48 else 0x4c
  let movModrm := 0xc0 + (pr % 8) * 8 + 2
  ins := ins.push (← `(show StepEffect _ _
    (movR64R64Effect ($pc + $(Lean.quote pos)) 2 $(Lean.quote pr)) from
      mov_r64_r64_effect_step ($pc + $(Lean.quote pos)) $(Lean.quote movRex)
        $(Lean.quote movModrm) (by simp [RexWPrefix]) rfl), 3)
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  pos := 0
  for (step, len) in ins do
    let first := pos = 0
    pos := pos + len
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn))
  let mut result ← `(tactic| advance_finish [Mark.effect])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

set_option maxHeartbeats 1000000 in
theorem Mark.run [Bindings] (p : BitVec 64) (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes v).length) :
    AdvanceTriple boundary (Pre p v) (codeRange p (bytes v))
      (Effect.post (effect p v)) := by
  cases v with
  | digest => sha256_finalize_mark 0, 12, 15, p, outside, inside
  | reset => sha256_finalize_mark 0, 15, 3, p, outside, inside
  | finalizeFirst => sha256_finalize_mark 8, 12, 3, p, outside, inside
  | finalizeLast => sha256_finalize_mark 112, 15, 14, p, outside, inside
  | traitFirst => sha256_finalize_mark 112, 15, 3, p, outside, inside
  | traitLast => sha256_finalize_mark 0, 15, 14, p, outside, inside

end Sha2.Proofs.Common.SHA256.Finalize
