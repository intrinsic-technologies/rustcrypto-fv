import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part20 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116969 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11696c 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11696f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116971 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116974 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116976 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116979 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11697b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11697e 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116981 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116984 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116988 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11698b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11698e 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116991 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116994 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116998 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11699a 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11699e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1169a0 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169a3 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1169a5 2 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1169a9 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169ab 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169ae 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169b1 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169b4 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169b7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169b9 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169bc 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169bf 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169c1 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1169c4 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1169c7 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1169ca 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1169cd 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1169cf 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169d1 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169d4 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1169d7 0x44 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x1169db 0x41 0xc2 0x983e5152 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169e2 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169e5 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169e8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169ea 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1169ed 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169f0 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1169f2 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1169f5 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1169f8 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1169fa 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1169fc 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1169ff 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116a02 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a04 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a07 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a0a 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a0e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116a11 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a14 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116a17 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a1a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a1d 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a20 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part20Bytes : List UInt8 :=
  [0x41,0x1,0xc4,0x41,0x1,0xc0,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xe8,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf2,0x41,0xc1,0xc2,0xe,0x41,0x31,0xca,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xd1,0x1,0x6c,0x24,0x24,0x1,0xe9,0x89,0x4c,0x24,0x14,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x34,0x1,0xca,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x1,0xd6,0x1,0xce,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x8d,0x14,0x30,0x41,0x81,0xc2,0x52,0x51,0x3e,0x98,0x44,0x89,0xc0,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0xa,0x31,0xc1,0x41,0x89,0xdb,0x41,0x21,0xfb,0x89,0xd8,0x31,0xf8,0x44,0x21,0xc0,0x44,0x31,0xd8,0x1,0xc8,0x45,0x1,0xd5,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xf,0x44,0x1,0xd0,0x48,0x89,0xc6,0x44,0x89,0xf1,0xc1,0xc1,0xd,0x44,0x31,0xd9,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x19]

set_option maxRecDepth 4096 in
theorem part20_bytes [Bindings] : part20.flatMap CheckedInstruction.bytes = part20Bytes  := by
  rfl

def part20Layout : List (BitVec 64 × Nat) :=
  [(0x116969, 3), (0x11696c, 3), (0x11696f, 2), (0x116971, 3), (0x116974, 2), (0x116976, 3), (0x116979, 2), (0x11697b, 3), (0x11697e, 3), (0x116981, 3), (0x116984, 4), (0x116988, 3), (0x11698b, 3), (0x11698e, 3), (0x116991, 3), (0x116994, 4), (0x116998, 2), (0x11699a, 4), (0x11699e, 2), (0x1169a0, 3), (0x1169a3, 2), (0x1169a5, 4), (0x1169a9, 2), (0x1169ab, 3), (0x1169ae, 3), (0x1169b1, 3), (0x1169b4, 3), (0x1169b7, 2), (0x1169b9, 3), (0x1169bc, 3), (0x1169bf, 2), (0x1169c1, 3), (0x1169c4, 3), (0x1169c7, 3), (0x1169ca, 3), (0x1169cd, 2), (0x1169cf, 2), (0x1169d1, 3), (0x1169d4, 3), (0x1169d7, 4), (0x1169db, 7), (0x1169e2, 3), (0x1169e5, 3), (0x1169e8, 2), (0x1169ea, 3), (0x1169ed, 3), (0x1169f0, 2), (0x1169f2, 3), (0x1169f5, 3), (0x1169f8, 2), (0x1169fa, 2), (0x1169fc, 3), (0x1169ff, 3), (0x116a02, 2), (0x116a04, 3), (0x116a07, 3), (0x116a0a, 4), (0x116a0e, 3), (0x116a11, 3), (0x116a14, 3), (0x116a17, 3), (0x116a1a, 3), (0x116a1d, 3), (0x116a20, 4)]

theorem part20_layout [Bindings] : InstructionTrace.layout part20 = part20Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part20_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16969 187 = part20Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
