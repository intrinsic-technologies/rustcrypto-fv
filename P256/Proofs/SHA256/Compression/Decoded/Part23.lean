import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part23 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bc8 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bcb 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116bce 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bd0 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x116bd3 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bd5 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116bd8 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116bdb 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116bde 0x43 (by simp [RexNoWPrefix]) 1 (.sib 9 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116be2 0xc1 0xbf597fc7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116be8 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116beb 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116bef 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116bf2 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bf6 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116bf9 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116bfc 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c00 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c03 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116c06 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c09 0x45 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c0c 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116c0f 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c12 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c15 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c18 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c1b 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c1e 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116c21 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116c25 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116c27 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c2a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c2d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116c30 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c34 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116c37 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c3b 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c3e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116c41 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c45 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116c48 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c4c 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x116c4f 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c57 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116c5a 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c5e 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116c61 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c65 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c68 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116c6b 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c6e 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116c71 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c75 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c78 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116c7b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c7e 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c81 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c84 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116c87 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116c8a 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c8d 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c90 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116c93 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116c96 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part23Bytes : List UInt8 :=
  [0x44,0x31,0xd1,0x41,0x31,0xc9,0x89,0xf9,0x44,0x31,0xe9,0x21,0xd9,0x44,0x31,0xe9,0x41,0x1,0xc4,0x41,0x1,0xcc,0x43,0x8d,0xc,0x21,0x81,0xc1,0xc7,0x7f,0x59,0xbf,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x13,0x45,0x31,0xca,0x41,0x89,0xf1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd1,0x45,0x89,0xf2,0x45,0x21,0xfa,0x45,0x89,0xf4,0x45,0x31,0xfc,0x41,0x21,0xf4,0x45,0x31,0xd4,0x45,0x1,0xcc,0x41,0x1,0xc8,0x41,0x1,0xcc,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc9,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x19,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xe,0x45,0x31,0xca,0x41,0x89,0xc1,0x41,0xc1,0xe9,0x3,0x45,0x31,0xd1,0x1,0x6c,0x24,0x8,0x41,0x1,0xe9,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x41,0x89,0xe9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xc9,0x8b,0x6c,0x24,0x10,0x44,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x1a,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x44,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x41,0x89,0xd9,0x41,0x31,0xf9,0x45,0x21,0xc1,0x41,0x31,0xf9,0x41,0x1,0xed,0x45,0x1,0xcd,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x1e]

set_option maxRecDepth 4096 in
theorem part23_bytes [Bindings] : part23.flatMap CheckedInstruction.bytes = part23Bytes  := by
  rfl

def part23Layout : List (BitVec 64 × Nat) :=
  [(0x116bc8, 3), (0x116bcb, 3), (0x116bce, 2), (0x116bd0, 3), (0x116bd3, 2), (0x116bd5, 3), (0x116bd8, 3), (0x116bdb, 3), (0x116bde, 4), (0x116be2, 6), (0x116be8, 3), (0x116beb, 4), (0x116bef, 3), (0x116bf2, 4), (0x116bf6, 3), (0x116bf9, 3), (0x116bfc, 4), (0x116c00, 3), (0x116c03, 3), (0x116c06, 3), (0x116c09, 3), (0x116c0c, 3), (0x116c0f, 3), (0x116c12, 3), (0x116c15, 3), (0x116c18, 3), (0x116c1b, 3), (0x116c1e, 3), (0x116c21, 4), (0x116c25, 2), (0x116c27, 3), (0x116c2a, 3), (0x116c2d, 3), (0x116c30, 4), (0x116c34, 3), (0x116c37, 4), (0x116c3b, 3), (0x116c3e, 3), (0x116c41, 4), (0x116c45, 3), (0x116c48, 4), (0x116c4c, 3), (0x116c4f, 8), (0x116c57, 3), (0x116c5a, 4), (0x116c5e, 3), (0x116c61, 4), (0x116c65, 3), (0x116c68, 3), (0x116c6b, 3), (0x116c6e, 3), (0x116c71, 4), (0x116c75, 3), (0x116c78, 3), (0x116c7b, 3), (0x116c7e, 3), (0x116c81, 3), (0x116c84, 3), (0x116c87, 3), (0x116c8a, 3), (0x116c8d, 3), (0x116c90, 3), (0x116c93, 3), (0x116c96, 4)]

theorem part23_layout [Bindings] : InstructionTrace.layout part23 = part23Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part23_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16bc8 210 = part23Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
