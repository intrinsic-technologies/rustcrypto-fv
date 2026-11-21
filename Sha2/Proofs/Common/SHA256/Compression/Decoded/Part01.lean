import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part01 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5fb 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5fd 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5ff 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b601 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b604 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b607 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b60a 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10b60c 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b60e 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b616 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b619 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10b61b 6 (.sib 1 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b61e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b620 0xc7 0x71374491 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b626 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b628 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b62b 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b62e 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b632 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b635 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b638 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b63c 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b63f 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b642 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b645 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b647 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b64a 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b652 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b654 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b657 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b65a 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b65c 0x45 (by simp [RexNoWPrefix]) 0 (.sib 14 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10b660 0x41 0xc0 0x71374491 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b667 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b66a 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b66d 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b670 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b673 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b675 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b678 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b67b 0xfe rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b67d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b682 0x44 (by simp [RexNoWPrefix]) 1 (.base 7 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b686 9) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b689 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b68e 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b691 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b693 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b696 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b699 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10b69c 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b69f 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b6a7 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b6aa 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6ad 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b6b0 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6b4 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b6b7 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b6bb 0x44 (by simp [RexNoWPrefix]) 3 (.sib 7 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b6bf 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b6c1 0xc7 0xb5c0fbcf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b6c7 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b6ca 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6cc 0xc3 0xa rfl rfl) (by x86_local)]

def part01Bytes : List UInt8 :=
  [0x31,0xce,0x31,0xf7,0x89,0xd1,0x44,0x21,0xe1,0x44,0x1,0xc9,0x44,0x1,0xe9,0x89,0xd6,0xf7,0xd6,0x4c,0x89,0x94,0x24,0x0,0x1,0x0,0x0,0x44,0x21,0xd6,0x1,0xf1,0x8d,0x34,0x39,0x1,0xcf,0x81,0xc7,0x91,0x44,0x37,0x71,0x89,0xc1,0xc1,0xc1,0x1e,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x41,0x89,0xc1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd8,0x45,0x21,0xf8,0x89,0xd9,0x44,0x31,0xf9,0x4c,0x89,0xbc,0x24,0xf8,0x0,0x0,0x0,0x21,0xc1,0x44,0x31,0xc1,0x44,0x1,0xc9,0x1,0xf9,0x45,0x8d,0x4,0x36,0x41,0x81,0xc0,0x91,0x44,0x37,0x71,0x44,0x89,0xc6,0xc1,0xc6,0x1a,0x44,0x89,0xc7,0xc1,0xc7,0x15,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0x7,0x31,0xfe,0x48,0x8b,0x7c,0x24,0x18,0x44,0x8b,0x4f,0x8,0x41,0xf,0xc9,0x4c,0x89,0x4c,0x24,0x68,0x44,0x89,0xc7,0x21,0xd7,0x45,0x1,0xd1,0x44,0x1,0xcf,0x45,0x89,0xc1,0x41,0xf7,0xd1,0x4c,0x89,0xa4,0x24,0xf0,0x0,0x0,0x0,0x45,0x21,0xe1,0x44,0x1,0xcf,0x41,0x89,0xc9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xca,0x41,0xc1,0xc2,0x13,0x44,0x8d,0x1c,0x37,0x1,0xf7,0x81,0xc7,0xcf,0xfb,0xc0,0xb5,0x48,0x89,0xde,0x89,0xcb,0xc1,0xc3,0xa]

set_option maxRecDepth 4096 in
theorem part01_bytes [Bindings] : part01.flatMap CheckedInstruction.bytes = part01Bytes  := by
  rfl

def part01Layout : List (BitVec 64 × Nat) :=
  [(0x10b5fb, 2), (0x10b5fd, 2), (0x10b5ff, 2), (0x10b601, 3), (0x10b604, 3), (0x10b607, 3), (0x10b60a, 2), (0x10b60c, 2), (0x10b60e, 8), (0x10b616, 3), (0x10b619, 2), (0x10b61b, 3), (0x10b61e, 2), (0x10b620, 6), (0x10b626, 2), (0x10b628, 3), (0x10b62b, 3), (0x10b62e, 4), (0x10b632, 3), (0x10b635, 3), (0x10b638, 4), (0x10b63c, 3), (0x10b63f, 3), (0x10b642, 3), (0x10b645, 2), (0x10b647, 3), (0x10b64a, 8), (0x10b652, 2), (0x10b654, 3), (0x10b657, 3), (0x10b65a, 2), (0x10b65c, 4), (0x10b660, 7), (0x10b667, 3), (0x10b66a, 3), (0x10b66d, 3), (0x10b670, 3), (0x10b673, 2), (0x10b675, 3), (0x10b678, 3), (0x10b67b, 2), (0x10b67d, 5), (0x10b682, 4), (0x10b686, 3), (0x10b689, 5), (0x10b68e, 3), (0x10b691, 2), (0x10b693, 3), (0x10b696, 3), (0x10b699, 3), (0x10b69c, 3), (0x10b69f, 8), (0x10b6a7, 3), (0x10b6aa, 3), (0x10b6ad, 3), (0x10b6b0, 4), (0x10b6b4, 3), (0x10b6b7, 4), (0x10b6bb, 4), (0x10b6bf, 2), (0x10b6c1, 6), (0x10b6c7, 3), (0x10b6ca, 2), (0x10b6cc, 3)]

theorem part01_layout [Bindings] : InstructionTrace.layout part01 = part01Layout := by
  rfl

theorem part01_ordered [Bindings] : InstructionTrace.ordered 0x10b5fb part01 = true := by
  rw [InstructionTrace.ordered_eq_layout, part01_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part01_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb5fb 212 = part01Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
