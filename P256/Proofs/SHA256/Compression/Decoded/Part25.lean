import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part25 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_effect_step 0x116d54 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d56 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116d59 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116d5c 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116d5f 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116d62 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d65 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d67 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116d6a 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d6d 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d6f 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116d72 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d75 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d77 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d7a 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d7c 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d7e 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d81 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d83 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116d85 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d88 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116d8a 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116d8e 0xef rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116d90 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116d94 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116d96 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d99 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d9b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d9e 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116da1 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116da5 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116da7 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116daa 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116dad 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116daf 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116db2 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116db5 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116db7 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116dba 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116dbd 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116dc0 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116dc3 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116dc5 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x116dc7 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116dca 0xc2 0x6ca6351 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116dd0 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116dd3 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116dd6 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116dd9 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116ddc 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116dde 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116de1 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116de4 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116de6 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116de9 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116dec 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116def 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116df2 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116df5 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116df8 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116dfa 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116dfd 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e00 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e02 0xc1 0xd rfl rfl) (by x86_local)]

def part25Bytes : List UInt8 :=
  [0x21,0xf2,0x45,0x89,0xe3,0x41,0x31,0xf3,0x45,0x21,0xcb,0x41,0x31,0xd3,0x41,0x1,0xcb,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xfe,0x89,0xe9,0xc1,0xc1,0xd,0x41,0x1,0xfb,0x89,0xc7,0xc1,0xc7,0x19,0x31,0xd1,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xc7,0xc1,0xef,0x3,0x31,0xd7,0x1,0x6c,0x24,0x50,0x1,0xef,0x89,0x7c,0x24,0x10,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x4,0x1,0xd5,0x44,0x89,0xf2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xfa,0x44,0x31,0xc2,0x44,0x21,0xf2,0x44,0x31,0xc2,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0x51,0x63,0xca,0x6,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xf9,0x44,0x89,0xcf,0x44,0x21,0xe7,0x45,0x89,0xcd,0x45,0x31,0xe5,0x45,0x21,0xdd,0x41,0x31,0xfd,0x89,0xc7,0xc1,0xc7,0xf,0x41,0x1,0xcd,0x89,0xc1,0xc1,0xc1,0xd]

set_option maxRecDepth 4096 in
theorem part25_bytes [Bindings] : part25.flatMap CheckedInstruction.bytes = part25Bytes  := by
  rfl

def part25Layout : List (BitVec 64 × Nat) :=
  [(0x116d54, 2), (0x116d56, 3), (0x116d59, 3), (0x116d5c, 3), (0x116d5f, 3), (0x116d62, 3), (0x116d65, 2), (0x116d67, 3), (0x116d6a, 3), (0x116d6d, 2), (0x116d6f, 3), (0x116d72, 3), (0x116d75, 2), (0x116d77, 3), (0x116d7a, 2), (0x116d7c, 2), (0x116d7e, 3), (0x116d81, 2), (0x116d83, 2), (0x116d85, 3), (0x116d88, 2), (0x116d8a, 4), (0x116d8e, 2), (0x116d90, 4), (0x116d94, 2), (0x116d96, 3), (0x116d99, 2), (0x116d9b, 3), (0x116d9e, 3), (0x116da1, 4), (0x116da5, 2), (0x116da7, 3), (0x116daa, 3), (0x116dad, 2), (0x116daf, 3), (0x116db2, 3), (0x116db5, 2), (0x116db7, 3), (0x116dba, 3), (0x116dbd, 3), (0x116dc0, 3), (0x116dc3, 2), (0x116dc5, 2), (0x116dc7, 3), (0x116dca, 6), (0x116dd0, 3), (0x116dd3, 3), (0x116dd6, 3), (0x116dd9, 3), (0x116ddc, 2), (0x116dde, 3), (0x116de1, 3), (0x116de4, 2), (0x116de6, 3), (0x116de9, 3), (0x116dec, 3), (0x116def, 3), (0x116df2, 3), (0x116df5, 3), (0x116df8, 2), (0x116dfa, 3), (0x116dfd, 3), (0x116e00, 2), (0x116e02, 3)]

theorem part25_layout [Bindings] : InstructionTrace.layout part25 = part25Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part25_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16d54 177 = part25Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
