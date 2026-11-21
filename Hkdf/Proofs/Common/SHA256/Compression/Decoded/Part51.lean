import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part51 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcae 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcb1 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcb3 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bcb6 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcb9 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bcbc 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bcbf 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bcc2 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bcc5 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bcc8 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bccb 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcce 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcd1 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcd4 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcd7 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcda 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcdd 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bcdf 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bce2 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bce4 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bce7 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcea 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bced 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcf0 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcf2 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcf5 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcf8 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bcfa 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bcff 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd01 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd04 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd07 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bd0a 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd0d 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd10 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bd13 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bd15 0xc7 0xc67178f2 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd1b 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bd1e 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd22 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd25 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd28 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd2b 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bd2e 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd32 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd35 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bd37 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd3a 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd3c 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bd3f 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd42 0xdd rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10bd44 5 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd4b 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bd4e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bd53 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10bd5b 0 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bd62 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bd6a 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd72 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bd74 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd76 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd79 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bd7c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10bd84 2 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part51Bytes : List UInt8 :=
  [0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xcb,0x44,0x21,0xdb,0x45,0x89,0xce,0x45,0x31,0xde,0x41,0x21,0xc6,0x41,0x31,0xde,0x41,0x1,0xee,0x41,0x1,0xfa,0x41,0x1,0xfe,0x44,0x89,0xfe,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xee,0xa,0x31,0xde,0x44,0x89,0xd7,0xc1,0xc7,0x1a,0x44,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x28,0x1,0xf3,0x44,0x1,0xc3,0x41,0x89,0xd0,0x41,0x31,0xc8,0x45,0x21,0xd0,0x41,0x31,0xc8,0x44,0x1,0xc3,0x1,0xdf,0x81,0xc7,0xf2,0x78,0x71,0xc6,0x45,0x89,0xf0,0x41,0xc1,0xc0,0x1e,0x44,0x89,0xf3,0xc1,0xc3,0x13,0x44,0x31,0xc3,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xd8,0x89,0xc3,0x44,0x21,0xcb,0x89,0xc5,0x44,0x31,0xcd,0x44,0x21,0xf5,0x31,0xdd,0x3,0xac,0x24,0xe8,0x0,0x0,0x0,0x44,0x1,0xc5,0x48,0x8b,0x74,0x24,0x18,0x44,0x3,0xb4,0x24,0xf8,0x0,0x0,0x0,0x3,0x84,0x24,0x8,0x1,0x0,0x0,0x44,0x3,0x8c,0x24,0x18,0x1,0x0,0x0,0x44,0x3,0x9c,0x24,0xf0,0x0,0x0,0x0,0x89,0xeb,0x1,0xfb,0x45,0x89,0xd8,0x41,0x1,0xf8,0x44,0x3,0x94,0x24,0x0,0x1,0x0,0x0,0x3,0x94,0x24,0x10,0x1,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part51_bytes [Bindings] : part51.flatMap CheckedInstruction.bytes = part51Bytes  := by
  rfl

def part51Layout : List (BitVec 64 × Nat) :=
  [(0x10bcae, 3), (0x10bcb1, 2), (0x10bcb3, 3), (0x10bcb6, 3), (0x10bcb9, 3), (0x10bcbc, 3), (0x10bcbf, 3), (0x10bcc2, 3), (0x10bcc5, 3), (0x10bcc8, 3), (0x10bccb, 3), (0x10bcce, 3), (0x10bcd1, 3), (0x10bcd4, 3), (0x10bcd7, 3), (0x10bcda, 3), (0x10bcdd, 2), (0x10bcdf, 3), (0x10bce2, 2), (0x10bce4, 3), (0x10bce7, 3), (0x10bcea, 3), (0x10bced, 3), (0x10bcf0, 2), (0x10bcf2, 3), (0x10bcf5, 3), (0x10bcf8, 2), (0x10bcfa, 5), (0x10bcff, 2), (0x10bd01, 3), (0x10bd04, 3), (0x10bd07, 3), (0x10bd0a, 3), (0x10bd0d, 3), (0x10bd10, 3), (0x10bd13, 2), (0x10bd15, 6), (0x10bd1b, 3), (0x10bd1e, 4), (0x10bd22, 3), (0x10bd25, 3), (0x10bd28, 3), (0x10bd2b, 3), (0x10bd2e, 4), (0x10bd32, 3), (0x10bd35, 2), (0x10bd37, 3), (0x10bd3a, 2), (0x10bd3c, 3), (0x10bd3f, 3), (0x10bd42, 2), (0x10bd44, 7), (0x10bd4b, 3), (0x10bd4e, 5), (0x10bd53, 8), (0x10bd5b, 7), (0x10bd62, 8), (0x10bd6a, 8), (0x10bd72, 2), (0x10bd74, 2), (0x10bd76, 3), (0x10bd79, 3), (0x10bd7c, 8), (0x10bd84, 7)]

theorem part51_layout [Bindings] : InstructionTrace.layout part51 = part51Layout := by
  rfl

theorem part51_ordered [Bindings] : InstructionTrace.ordered 0x10bcae part51 = true := by
  rw [InstructionTrace.ordered_eq_layout, part51_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part51_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xbcae 221 = part51Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
