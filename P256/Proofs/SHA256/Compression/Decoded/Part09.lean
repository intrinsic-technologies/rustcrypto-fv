import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part09 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1160a7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160a9 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1160ac 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1160ae 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160b0 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1160b3 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1160b5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1160ba 5 (.base 1 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x1160bd 5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1160bf 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1160c1 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1160c3 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1160c6 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1160c9 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x1160cb 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1160cd 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1160d0 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1160d3 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x1160d7 0xc1 0x9bdc06a7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1160dd 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160e0 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1160e3 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160e6 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1160e9 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1160eb 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160ee 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1160f1 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1160f3 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1160f6 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1160f8 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1160fb 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1160fe 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116101 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116104 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116107 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11610a 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11610d 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116110 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116113 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116116 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116119 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11611c 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11611e 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116121 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116124 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116126 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x11612b 0x44 (by simp [RexNoWPrefix]) 5 (.base 6 (.d8 60)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x11612f 13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116132 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x116135 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116137 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11613a 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11613d 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x116140 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x116142 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116144 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116147 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11614a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11614d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116150 0xc1 0xc19bf174 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116156 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116159 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11615c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11615e 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part09Bytes : List UInt8 :=
  [0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x38,0xf,0xcd,0x89,0xd1,0x21,0xc1,0x41,0x1,0xeb,0x41,0x1,0xcb,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xd1,0x41,0x1,0xcb,0x42,0x8d,0xc,0x1e,0x81,0xc1,0xa7,0x6,0xdc,0x9b,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xcf,0x21,0xdf,0x45,0x89,0xc8,0x41,0x31,0xd8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xcf,0x41,0x1,0xc8,0x4d,0x89,0xc3,0x44,0x89,0xf9,0xc1,0xc1,0x1a,0x44,0x89,0xfe,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x44,0x8b,0x6e,0x3c,0x41,0xf,0xcd,0x44,0x89,0xfe,0x21,0xd6,0x45,0x1,0xea,0x41,0x1,0xf2,0x44,0x89,0xfe,0xf7,0xd6,0x21,0xc6,0x41,0x1,0xf2,0x44,0x89,0xde,0xc1,0xc6,0x1e,0x44,0x1,0xd1,0x81,0xc1,0x74,0xf1,0x9b,0xc1,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xde]

set_option maxRecDepth 4096 in
theorem part09_bytes [Bindings] : part09.flatMap CheckedInstruction.bytes = part09Bytes  := by
  rfl

def part09Layout : List (BitVec 64 × Nat) :=
  [(0x1160a7, 2), (0x1160a9, 3), (0x1160ac, 2), (0x1160ae, 2), (0x1160b0, 3), (0x1160b3, 2), (0x1160b5, 5), (0x1160ba, 3), (0x1160bd, 2), (0x1160bf, 2), (0x1160c1, 2), (0x1160c3, 3), (0x1160c6, 3), (0x1160c9, 2), (0x1160cb, 2), (0x1160cd, 3), (0x1160d0, 3), (0x1160d3, 4), (0x1160d7, 6), (0x1160dd, 3), (0x1160e0, 3), (0x1160e3, 3), (0x1160e6, 3), (0x1160e9, 2), (0x1160eb, 3), (0x1160ee, 3), (0x1160f1, 2), (0x1160f3, 3), (0x1160f6, 2), (0x1160f8, 3), (0x1160fb, 3), (0x1160fe, 3), (0x116101, 3), (0x116104, 3), (0x116107, 3), (0x11610a, 3), (0x11610d, 3), (0x116110, 3), (0x116113, 3), (0x116116, 3), (0x116119, 3), (0x11611c, 2), (0x11611e, 3), (0x116121, 3), (0x116124, 2), (0x116126, 5), (0x11612b, 4), (0x11612f, 3), (0x116132, 3), (0x116135, 2), (0x116137, 3), (0x11613a, 3), (0x11613d, 3), (0x116140, 2), (0x116142, 2), (0x116144, 3), (0x116147, 3), (0x11614a, 3), (0x11614d, 3), (0x116150, 6), (0x116156, 3), (0x116159, 3), (0x11615c, 2), (0x11615e, 3)]

theorem part09_layout [Bindings] : InstructionTrace.layout part09 = part09Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part09_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x160a7 186 = part09Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
