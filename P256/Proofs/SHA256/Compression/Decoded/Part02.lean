import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part02 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115b7f 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115b82 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b85 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115b88 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115b8b 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115b8e 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115b90 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115b93 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115b96 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115b9e 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115ba0 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115ba3 0x47 (by simp [RexNoWPrefix]) 2 (.sib 15 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x115ba7 0x41 0xc2 0xb5c0fbcf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115bae 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115bb1 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115bb5 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115bb7 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115bba 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115bbe 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115bc0 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115bc3 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115bc6 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115bc9 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115bcc 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x115bd1 0x45 (by simp [RexNoWPrefix]) 3 (.base 9 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115bd5 11) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115bd8 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115bdd 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115be0 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115be3 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115be6 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115be9 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x115bec 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115bef 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115bf2 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115bf5 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115bf8 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115bfc 0x41 (by simp [RexNoWPrefix]) 3 (.sib 9 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c00 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x115c03 0x41 0xc1 0xe9b5dba5 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115c0a 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115c0c 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c0f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c12 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c15 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c19 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115c1c 0xcd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115c1e 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115c20 0xcf rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115c22 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115c24 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115c26 0xef rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c28 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c2b 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115c2e 0xc3 0xe9b5dba5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c34 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c37 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c3b 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c3e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c41 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c45 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c48 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c4b 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c4f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part02Bytes : List UInt8 :=
  [0x45,0x31,0xca,0x44,0x31,0xd3,0x41,0x89,0xc1,0x49,0x89,0xf2,0x45,0x21,0xd1,0x89,0xc6,0x44,0x31,0xd6,0x4d,0x89,0xd6,0x4c,0x89,0x94,0x24,0xe8,0x0,0x0,0x0,0x21,0xce,0x44,0x31,0xce,0x47,0x8d,0x14,0x1f,0x41,0x81,0xc2,0xcf,0xfb,0xc0,0xb5,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x1,0xde,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x15,0x1,0xfe,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x45,0x31,0xcb,0x44,0x31,0xdf,0x4c,0x8b,0x4c,0x24,0x18,0x45,0x8b,0x59,0xc,0x41,0xf,0xcb,0x4c,0x89,0x5c,0x24,0x48,0x45,0x89,0xd1,0x45,0x21,0xc1,0x45,0x1,0xe3,0x45,0x1,0xd9,0x45,0x89,0xd3,0x41,0xf7,0xd3,0x41,0x21,0xd3,0x45,0x1,0xd9,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x1e,0x41,0x8d,0x1c,0x39,0x41,0x1,0xf9,0x41,0x81,0xc1,0xa5,0xdb,0xb5,0xe9,0x89,0xf7,0xc1,0xc7,0x13,0x44,0x31,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0xa,0x41,0x31,0xfb,0x89,0xcd,0x21,0xc5,0x89,0xcf,0x31,0xc7,0x21,0xf7,0x31,0xef,0x44,0x1,0xdf,0x44,0x1,0xf3,0x81,0xc3,0xa5,0xdb,0xb5,0xe9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x1a,0x44,0x1,0xcf,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x15,0x45,0x31,0xd9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x7,0x45,0x31,0xcb]

set_option maxRecDepth 4096 in
theorem part02_bytes [Bindings] : part02.flatMap CheckedInstruction.bytes = part02Bytes  := by
  rfl

def part02Layout : List (BitVec 64 × Nat) :=
  [(0x115b7f, 3), (0x115b82, 3), (0x115b85, 3), (0x115b88, 3), (0x115b8b, 3), (0x115b8e, 2), (0x115b90, 3), (0x115b93, 3), (0x115b96, 8), (0x115b9e, 2), (0x115ba0, 3), (0x115ba3, 4), (0x115ba7, 7), (0x115bae, 3), (0x115bb1, 4), (0x115bb5, 2), (0x115bb7, 3), (0x115bba, 4), (0x115bbe, 2), (0x115bc0, 3), (0x115bc3, 3), (0x115bc6, 3), (0x115bc9, 3), (0x115bcc, 5), (0x115bd1, 4), (0x115bd5, 3), (0x115bd8, 5), (0x115bdd, 3), (0x115be0, 3), (0x115be3, 3), (0x115be6, 3), (0x115be9, 3), (0x115bec, 3), (0x115bef, 3), (0x115bf2, 3), (0x115bf5, 3), (0x115bf8, 4), (0x115bfc, 4), (0x115c00, 3), (0x115c03, 7), (0x115c0a, 2), (0x115c0c, 3), (0x115c0f, 3), (0x115c12, 3), (0x115c15, 4), (0x115c19, 3), (0x115c1c, 2), (0x115c1e, 2), (0x115c20, 2), (0x115c22, 2), (0x115c24, 2), (0x115c26, 2), (0x115c28, 3), (0x115c2b, 3), (0x115c2e, 6), (0x115c34, 3), (0x115c37, 4), (0x115c3b, 3), (0x115c3e, 3), (0x115c41, 4), (0x115c45, 3), (0x115c48, 3), (0x115c4b, 4), (0x115c4f, 3)]

theorem part02_layout [Bindings] : InstructionTrace.layout part02 = part02Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part02_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15b7f 211 = part02Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
