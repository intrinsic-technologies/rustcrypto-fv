import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part50 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc03 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc06 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc08 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc0b 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc0d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc0f 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc12 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc14 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc17 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc19 0xcb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc1b 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc1d 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc20 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc22 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bc24 0xc7 0xa4506ceb rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc2a 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc2d 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc30 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc33 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc36 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc38 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bc3b 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc3f 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc42 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bc45 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc48 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc4b 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bc4e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc51 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc53 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc56 0xfa rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc58 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc5a 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc5d 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc60 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc63 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc66 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc69 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bc6b 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc6e 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc70 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc72 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc75 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc77 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc7a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc7c 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc7e 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc81 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bc83 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc88 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc8a 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc8c 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc8e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc91 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc93 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc96 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bc98 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bc9a 0xc7 0xbef9a3f7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bca0 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bca2 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bca5 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bca7 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcaa 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bcac 0xc5 rfl) (by x86_local)]

def part50Bytes : List UInt8 :=
  [0x41,0x1,0xef,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xcf,0xc1,0xc7,0x7,0x31,0xdf,0x44,0x89,0xc3,0x31,0xf3,0x21,0xcb,0x31,0xf3,0x44,0x1,0xf8,0x1,0xd8,0x1,0xc7,0x81,0xc7,0xeb,0x6c,0x50,0xa4,0x44,0x89,0xc8,0xc1,0xc0,0x1e,0x44,0x89,0xcb,0xc1,0xc3,0x13,0x31,0xc3,0x45,0x89,0xce,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xdb,0x44,0x21,0xd3,0x44,0x89,0xd8,0x44,0x31,0xd0,0x44,0x21,0xc8,0x31,0xd8,0x44,0x1,0xf0,0x1,0xfa,0x1,0xf8,0x44,0x89,0xe5,0x44,0x89,0xe7,0xc1,0xc7,0xf,0x44,0x89,0xe3,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xd7,0xc1,0xc7,0x1a,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x40,0x1,0xeb,0x1,0xf3,0x89,0xce,0x44,0x31,0xc6,0x21,0xd6,0x44,0x31,0xc6,0x1,0xf3,0x1,0xdf,0x81,0xc7,0xf7,0xa3,0xf9,0xbe,0x89,0xc6,0xc1,0xc6,0x1e,0x89,0xc3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xc5]

set_option maxRecDepth 4096 in
theorem part50_bytes [Bindings] : part50.flatMap CheckedInstruction.bytes = part50Bytes  := by
  rfl

def part50Layout : List (BitVec 64 × Nat) :=
  [(0x10bc03, 3), (0x10bc06, 2), (0x10bc08, 3), (0x10bc0b, 2), (0x10bc0d, 2), (0x10bc0f, 3), (0x10bc12, 2), (0x10bc14, 3), (0x10bc17, 2), (0x10bc19, 2), (0x10bc1b, 2), (0x10bc1d, 3), (0x10bc20, 2), (0x10bc22, 2), (0x10bc24, 6), (0x10bc2a, 3), (0x10bc2d, 3), (0x10bc30, 3), (0x10bc33, 3), (0x10bc36, 2), (0x10bc38, 3), (0x10bc3b, 4), (0x10bc3f, 3), (0x10bc42, 3), (0x10bc45, 3), (0x10bc48, 3), (0x10bc4b, 3), (0x10bc4e, 3), (0x10bc51, 2), (0x10bc53, 3), (0x10bc56, 2), (0x10bc58, 2), (0x10bc5a, 3), (0x10bc5d, 3), (0x10bc60, 3), (0x10bc63, 3), (0x10bc66, 3), (0x10bc69, 2), (0x10bc6b, 3), (0x10bc6e, 2), (0x10bc70, 2), (0x10bc72, 3), (0x10bc75, 2), (0x10bc77, 3), (0x10bc7a, 2), (0x10bc7c, 2), (0x10bc7e, 3), (0x10bc81, 2), (0x10bc83, 5), (0x10bc88, 2), (0x10bc8a, 2), (0x10bc8c, 2), (0x10bc8e, 3), (0x10bc91, 2), (0x10bc93, 3), (0x10bc96, 2), (0x10bc98, 2), (0x10bc9a, 6), (0x10bca0, 2), (0x10bca2, 3), (0x10bca5, 2), (0x10bca7, 3), (0x10bcaa, 2), (0x10bcac, 2)]

theorem part50_layout [Bindings] : InstructionTrace.layout part50 = part50Layout := by
  rfl

theorem part50_ordered [Bindings] : InstructionTrace.ordered 0x10bc03 part50 = true := by
  rw [InstructionTrace.ordered_eq_layout, part50_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part50_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xbc03 171 = part50Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
