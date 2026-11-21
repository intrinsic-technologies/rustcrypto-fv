import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part14

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part15 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e406 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1c43) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e40d 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e410 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e413 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e416 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e419 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e41c 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e41f 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e422 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e425 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e428 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e42c 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e42f 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e432 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e436 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e439 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e43c 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e440 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e443 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e446 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e449 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e44c 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e44f 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e452 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e455 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e458 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e45b 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e45e 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e462 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e465 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e468 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e46c 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e46f 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e472 0x48 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e476 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e479 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e47c 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e481 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e484 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part15Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0x43,0x1c,0xf,0x0,0x4c,0x1,0xf2,0x48,0x1,0xf2,0x4c,0x89,0xc6,0x48,0x21,0xfe,0x48,0x1,0xf2,0x4c,0x89,0xc6,0x48,0xf7,0xd6,0x4c,0x21,0xde,0x49,0x89,0xc6,0x49,0xc1,0xc6,0x24,0x48,0x1,0xf2,0x48,0x89,0xc6,0x48,0xc1,0xc6,0x1e,0x48,0x1,0xda,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xf6,0x48,0x31,0xf3,0x49,0x89,0xce,0x4d,0x21,0xd6,0x48,0x89,0xce,0x4c,0x31,0xd6,0x48,0x21,0xc6,0x4c,0x31,0xf6,0x49,0x1,0xd1,0x4d,0x89,0xce,0x49,0xc1,0xc6,0x32,0x48,0x1,0xde,0x4d,0x89,0xcf,0x49,0xc1,0xc7,0x2e,0x48,0x1,0xd6,0x4c,0x89,0xcb,0x48,0xc1,0xc3,0x17,0x4d,0x31,0xf7,0x4c,0x31,0xfb,0x4c,0x8b,0x74,0x24,0x40,0x49,0xf,0xce,0x4c,0x89,0x74,0x24,0x40]

def part15Layout : List (BitVec 64 × Nat) :=
  [(0x10e406, 7), (0x10e40d, 3), (0x10e410, 3), (0x10e413, 3), (0x10e416, 3),
   (0x10e419, 3), (0x10e41c, 3), (0x10e41f, 3), (0x10e422, 3), (0x10e425, 3),
   (0x10e428, 4), (0x10e42c, 3), (0x10e42f, 3), (0x10e432, 4), (0x10e436, 3),
   (0x10e439, 3), (0x10e43c, 4), (0x10e440, 3), (0x10e443, 3), (0x10e446, 3),
   (0x10e449, 3), (0x10e44c, 3), (0x10e44f, 3), (0x10e452, 3), (0x10e455, 3),
   (0x10e458, 3), (0x10e45b, 3), (0x10e45e, 4), (0x10e462, 3), (0x10e465, 3),
   (0x10e468, 4), (0x10e46c, 3), (0x10e46f, 3), (0x10e472, 4), (0x10e476, 3),
   (0x10e479, 3), (0x10e47c, 5), (0x10e481, 3), (0x10e484, 5)]

set_option maxRecDepth 4096 in
theorem part15_bytes [Bindings] : part15.flatMap CheckedInstruction.bytes = part15Bytes := by
  rfl

theorem part15_layout [Bindings] : InstructionTrace.layout part15 = part15Layout := by
  rfl

theorem part15_ordered [Bindings] : InstructionTrace.ordered 0x10e406 part15 = true := by
  rw [InstructionTrace.ordered_eq_layout, part15_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part15_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe406 131 = part15Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
