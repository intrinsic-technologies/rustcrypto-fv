import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part12 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1162e4 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1162e7 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x1162eb 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1162f0 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1162f3 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1162f6 0x41 0xc4 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1162fa 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1162fc 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116300 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116303 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116307 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116309 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11630c 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11630f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116314 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x116316 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11631b 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11631f 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116321 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116324 0xd5 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x116326 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11632e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116330 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116333 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116335 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116337 2 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11633b 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11633e 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116342 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116345 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116347 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11634a 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x11634d 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116352 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116355 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116358 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x11635b 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116363 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_effect_step 0x116367 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x11636c 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d32 180)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116374 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116377 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116379 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11637c 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x11637f 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 164)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116387 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11638a 0x41 0xc6 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11638e 0xcd rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116390 5 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116397 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11639b 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11639d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1163a0 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1163a3 2 (.sib 4 none 0 (.d32 156)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1163aa 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163ac 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1163af 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1163b2 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163b7 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163ba 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1163bd 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163c0 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163c3 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1163c6 0xca rfl) (by x86_local)]

def part12Bytes : List UInt8 :=
  [0x45,0x89,0xd3,0x41,0xc1,0xc3,0xf,0x44,0x89,0x5c,0x24,0x4,0x44,0x21,0xcd,0x45,0x89,0xd4,0x41,0xc1,0xc4,0xd,0x31,0xcd,0x8b,0x4c,0x24,0x60,0x41,0x89,0xca,0x41,0xc1,0xc2,0x19,0x1,0xf5,0xc1,0xc1,0xe,0x41,0x89,0xce,0x48,0x8b,0x4c,0x24,0x58,0x1,0xd1,0x48,0x89,0x4c,0x24,0x58,0x8b,0x74,0x24,0x8,0x89,0xf1,0xc1,0xc1,0x19,0x1,0xd5,0x48,0x89,0xac,0x24,0xd0,0x0,0x0,0x0,0x89,0xf2,0xc1,0xc2,0xe,0x89,0xd5,0x31,0xc7,0x8b,0x54,0x24,0xc,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x19,0xc1,0xc2,0xe,0x89,0xd8,0xc1,0xe8,0x3,0x41,0x89,0xc0,0x44,0x8b,0x5c,0x24,0x34,0x44,0x89,0xd8,0xc1,0xc0,0x19,0x41,0x31,0xf8,0x44,0x89,0x84,0x24,0xb8,0x0,0x0,0x0,0x41,0xc1,0xc3,0xe,0x44,0x33,0x64,0x24,0x4,0x44,0x89,0xa4,0x24,0xb4,0x0,0x0,0x0,0x8b,0x3c,0x24,0x89,0xfe,0xc1,0xc6,0x19,0x45,0x31,0xd6,0x44,0x89,0xb4,0x24,0xa4,0x0,0x0,0x0,0x41,0x89,0xfe,0x41,0xc1,0xc6,0xe,0x31,0xcd,0x89,0xac,0x24,0xa0,0x0,0x0,0x0,0x8b,0x6c,0x24,0x10,0x89,0xe9,0xc1,0xc1,0x19,0x44,0x31,0xca,0x89,0x94,0x24,0x9c,0x0,0x0,0x0,0x89,0xea,0xc1,0xc2,0xe,0x41,0x31,0xc3,0x44,0x8b,0x54,0x24,0x64,0x44,0x89,0xd7,0xc1,0xc7,0x19,0x41,0x31,0xf6,0x44,0x89,0xd0,0xc1,0xc0,0xe,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part12_bytes [Bindings] : part12.flatMap CheckedInstruction.bytes = part12Bytes  := by
  rfl

def part12Layout : List (BitVec 64 × Nat) :=
  [(0x1162e4, 3), (0x1162e7, 4), (0x1162eb, 5), (0x1162f0, 3), (0x1162f3, 3), (0x1162f6, 4), (0x1162fa, 2), (0x1162fc, 4), (0x116300, 3), (0x116303, 4), (0x116307, 2), (0x116309, 3), (0x11630c, 3), (0x11630f, 5), (0x116314, 2), (0x116316, 5), (0x11631b, 4), (0x11631f, 2), (0x116321, 3), (0x116324, 2), (0x116326, 8), (0x11632e, 2), (0x116330, 3), (0x116333, 2), (0x116335, 2), (0x116337, 4), (0x11633b, 3), (0x11633e, 4), (0x116342, 3), (0x116345, 2), (0x116347, 3), (0x11634a, 3), (0x11634d, 5), (0x116352, 3), (0x116355, 3), (0x116358, 3), (0x11635b, 8), (0x116363, 4), (0x116367, 5), (0x11636c, 8), (0x116374, 3), (0x116377, 2), (0x116379, 3), (0x11637c, 3), (0x11637f, 8), (0x116387, 3), (0x11638a, 4), (0x11638e, 2), (0x116390, 7), (0x116397, 4), (0x11639b, 2), (0x11639d, 3), (0x1163a0, 3), (0x1163a3, 7), (0x1163aa, 2), (0x1163ac, 3), (0x1163af, 3), (0x1163b2, 5), (0x1163b7, 3), (0x1163ba, 3), (0x1163bd, 3), (0x1163c0, 3), (0x1163c3, 3), (0x1163c6, 2)]

theorem part12_layout [Bindings] : InstructionTrace.layout part12 = part12Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part12_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x162e4 228 = part12Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
