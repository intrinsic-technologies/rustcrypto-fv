import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part35 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1174c1 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1174c5 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174c8 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1174cb 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1174cf 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x1174d2 0x41 0xc2 0xa81a664b (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1174d9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1174db 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174de 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174e1 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174e4 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1174e7 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174ea 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174ed 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1174f0 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174f3 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1174f6 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174f9 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1174fc 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117500 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117503 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117506 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117509 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11750c 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11750f 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117512 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117516 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117519 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11751c 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117520 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117523 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x117526 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11752a 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x11752d 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117532 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x117535 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11753a 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x11753d 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117541 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117544 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117546 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117549 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117550 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117553 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117556 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11755a 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11755d 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11755f 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117562 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117565 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117568 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11756b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11756e 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117571 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117574 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117577 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x11757a 0xc1 0xc24b8b70 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117580 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117583 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117587 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11758a 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11758e 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117591 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117594 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part35Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0x1e,0x45,0x1,0xc2,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x1,0xca,0x41,0x81,0xc2,0x4b,0x66,0x1a,0xa8,0x89,0xd9,0xc1,0xc1,0xa,0x45,0x31,0xc8,0x44,0x31,0xc1,0x45,0x89,0xd8,0x41,0x21,0xd0,0x45,0x89,0xdf,0x41,0x31,0xd7,0x41,0x21,0xdf,0x45,0x31,0xc7,0x41,0x1,0xcf,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xf,0x44,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0xd,0x45,0x1,0xd7,0x41,0x89,0xea,0x41,0x89,0xe9,0x41,0xc1,0xc1,0x19,0x44,0x31,0xc1,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xe,0x45,0x31,0xc8,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x45,0x31,0xc1,0x44,0x1,0x64,0x24,0x40,0x45,0x1,0xe1,0x44,0x89,0x4c,0x24,0x68,0x45,0x89,0xe0,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc5,0x41,0x89,0xf0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xc0,0x41,0x31,0xf8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xee,0x45,0x1,0xc6,0x44,0x1,0xf1,0x81,0xc1,0x70,0x8b,0x4b,0xc2,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1e,0x45,0x89,0xf9,0x41,0xc1,0xc1,0x13,0x45,0x31,0xc1,0x45,0x89,0xf8,0x41,0xc1,0xc0,0xa]

set_option maxRecDepth 4096 in
theorem part35_bytes [Bindings] : part35.flatMap CheckedInstruction.bytes = part35Bytes  := by
  rfl

def part35Layout : List (BitVec 64 × Nat) :=
  [(0x1174c1, 4), (0x1174c5, 3), (0x1174c8, 3), (0x1174cb, 4), (0x1174cf, 3), (0x1174d2, 7), (0x1174d9, 2), (0x1174db, 3), (0x1174de, 3), (0x1174e1, 3), (0x1174e4, 3), (0x1174e7, 3), (0x1174ea, 3), (0x1174ed, 3), (0x1174f0, 3), (0x1174f3, 3), (0x1174f6, 3), (0x1174f9, 3), (0x1174fc, 4), (0x117500, 3), (0x117503, 3), (0x117506, 3), (0x117509, 3), (0x11750c, 3), (0x11750f, 3), (0x117512, 4), (0x117516, 3), (0x117519, 3), (0x11751c, 4), (0x117520, 3), (0x117523, 3), (0x117526, 4), (0x11752a, 3), (0x11752d, 5), (0x117532, 3), (0x117535, 5), (0x11753a, 3), (0x11753d, 4), (0x117541, 3), (0x117544, 2), (0x117546, 3), (0x117549, 7), (0x117550, 3), (0x117553, 3), (0x117556, 4), (0x11755a, 3), (0x11755d, 2), (0x11755f, 3), (0x117562, 3), (0x117565, 3), (0x117568, 3), (0x11756b, 3), (0x11756e, 3), (0x117571, 3), (0x117574, 3), (0x117577, 3), (0x11757a, 6), (0x117580, 3), (0x117583, 4), (0x117587, 3), (0x11758a, 4), (0x11758e, 3), (0x117591, 3), (0x117594, 4)]

theorem part35_layout [Bindings] : InstructionTrace.layout part35 = part35Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part35_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x174c1 215 = part35Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
