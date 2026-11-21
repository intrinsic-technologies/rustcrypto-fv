import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part29 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11702d 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117030 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117033 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x117035 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117038 0xc2 0x4d2c6dfc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11703e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117041 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117044 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117047 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11704a 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11704c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11704f 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117052 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117054 0xce rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117056 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117059 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11705c 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11705f 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117062 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117065 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117067 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11706a 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11706d 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11706f 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117072 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117075 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117078 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11707b 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11707e 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117081 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117084 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117086 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117088 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11708b 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11708e 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117090 5 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117094 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x117096 6 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11709a 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11709c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11709f 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170a2 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170a5 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170a7 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170aa 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1170ad 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1170b1 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170b3 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170b6 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170b9 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170bb 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170bd 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1170c0 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1170c3 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1170c6 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1170c9 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1170cc 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1170cf 0x42 (by simp [RexNoWPrefix]) 0 (.sib 2 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x1170d3 0x53380d13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170d8 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170db 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170de 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170e1 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170e4 0xd6 rfl) (by x86_local)]

def part29Bytes : List UInt8 :=
  [0x44,0x31,0xe2,0x44,0x1,0xfe,0x1,0xd6,0x8d,0x14,0x30,0x81,0xc2,0xfc,0x6d,0x2c,0x4d,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd6,0xc1,0xc6,0x13,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0xa,0x31,0xf0,0x89,0xce,0x44,0x21,0xc6,0x41,0x89,0xce,0x45,0x31,0xc6,0x45,0x21,0xd6,0x41,0x31,0xf6,0x89,0xee,0xc1,0xc6,0xf,0x41,0x1,0xc6,0x89,0xe8,0xc1,0xc0,0xd,0x41,0x1,0xd5,0x44,0x89,0xff,0xc1,0xc7,0x19,0x41,0x1,0xd6,0x44,0x89,0xfa,0xc1,0xc2,0xe,0x31,0xf0,0x31,0xfa,0x44,0x89,0xfe,0xc1,0xee,0x3,0x31,0xd6,0x1,0x6c,0x24,0x70,0x1,0xee,0x89,0x74,0x24,0xc,0x89,0xea,0xc1,0xea,0xa,0x44,0x89,0xee,0xc1,0xc6,0x1a,0x31,0xc2,0x44,0x89,0xe8,0xc1,0xc0,0x15,0x8b,0x6c,0x24,0x50,0x1,0xd5,0x44,0x89,0xea,0xc1,0xc2,0x7,0x31,0xf0,0x31,0xc2,0x44,0x89,0xd8,0x44,0x31,0xc8,0x44,0x21,0xe8,0x44,0x31,0xc8,0x41,0x1,0xec,0x41,0x1,0xc4,0x42,0x8d,0x4,0x22,0x5,0x13,0xd,0x38,0x53,0x44,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xd6]

set_option maxRecDepth 4096 in
theorem part29_bytes [Bindings] : part29.flatMap CheckedInstruction.bytes = part29Bytes  := by
  rfl

def part29Layout : List (BitVec 64 × Nat) :=
  [(0x11702d, 3), (0x117030, 3), (0x117033, 2), (0x117035, 3), (0x117038, 6), (0x11703e, 3), (0x117041, 3), (0x117044, 3), (0x117047, 3), (0x11704a, 2), (0x11704c, 3), (0x11704f, 3), (0x117052, 2), (0x117054, 2), (0x117056, 3), (0x117059, 3), (0x11705c, 3), (0x11705f, 3), (0x117062, 3), (0x117065, 2), (0x117067, 3), (0x11706a, 3), (0x11706d, 2), (0x11706f, 3), (0x117072, 3), (0x117075, 3), (0x117078, 3), (0x11707b, 3), (0x11707e, 3), (0x117081, 3), (0x117084, 2), (0x117086, 2), (0x117088, 3), (0x11708b, 3), (0x11708e, 2), (0x117090, 4), (0x117094, 2), (0x117096, 4), (0x11709a, 2), (0x11709c, 3), (0x11709f, 3), (0x1170a2, 3), (0x1170a5, 2), (0x1170a7, 3), (0x1170aa, 3), (0x1170ad, 4), (0x1170b1, 2), (0x1170b3, 3), (0x1170b6, 3), (0x1170b9, 2), (0x1170bb, 2), (0x1170bd, 3), (0x1170c0, 3), (0x1170c3, 3), (0x1170c6, 3), (0x1170c9, 3), (0x1170cc, 3), (0x1170cf, 4), (0x1170d3, 5), (0x1170d8, 3), (0x1170db, 3), (0x1170de, 3), (0x1170e1, 3), (0x1170e4, 2)]

theorem part29_layout [Bindings] : InstructionTrace.layout part29 = part29Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part29_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1702d 185 = part29Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
