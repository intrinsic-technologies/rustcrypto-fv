import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part13 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163c8 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163cb 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1163ce 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163d0 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163d3 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1163d6 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1163d8 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163dd 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163e0 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163e3 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1163e6 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1163e9 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1163eb 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1163ee 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1163f1 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1163f3 0xf7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1163f5 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x1163f9 6 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x116400 6 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x116407 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11640e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116411 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116415 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116418 7 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x11641f 0x41 0xed 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116423 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116426 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x11642a 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x116431 1 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x116438 1 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11643f 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116442 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116445 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116449 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x11644c 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116451 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116454 0xc6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x116456 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11645b 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11645e 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116461 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116464 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116466 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116469 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11646c 0xc6 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11646e 6 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116472 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116475 0xd0 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116477 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11647a 0xd3 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11647c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116481 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116483 0 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116487 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11648a 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11648d 0 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116491 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116496 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116498 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11649a 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11649e 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1164a1 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1164a4 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1164a9 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part13Bytes : List UInt8 :=
  [0x44,0x89,0xee,0xc1,0xc6,0x19,0x31,0xf8,0x44,0x89,0xe9,0xc1,0xc1,0xe,0x31,0xf1,0x4c,0x8b,0x44,0x24,0x50,0x44,0x89,0xc6,0xc1,0xc6,0x19,0x44,0x89,0xc7,0xc1,0xc7,0xe,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xee,0x3,0x31,0xfe,0x89,0xf7,0x8b,0x74,0x24,0x28,0x89,0xb4,0x24,0xa8,0x0,0x0,0x0,0x89,0xb4,0x24,0xac,0x0,0x0,0x0,0x89,0xb4,0x24,0xb0,0x0,0x0,0x0,0x44,0x1,0xee,0x89,0x74,0x24,0x28,0x44,0x1,0xef,0x89,0xbc,0x24,0x8c,0x0,0x0,0x0,0x41,0xc1,0xed,0x3,0x41,0x31,0xcd,0x8b,0x4c,0x24,0x40,0x89,0x8c,0x24,0x90,0x0,0x0,0x0,0x89,0x8c,0x24,0x94,0x0,0x0,0x0,0x89,0x8c,0x24,0x98,0x0,0x0,0x0,0x44,0x89,0xd6,0x44,0x1,0xd1,0x89,0x4c,0x24,0x40,0x45,0x1,0xd5,0x44,0x89,0x6c,0x24,0x4,0xc1,0xee,0x3,0x31,0xc6,0x44,0x8b,0x4c,0x24,0x24,0x44,0x89,0xc9,0x45,0x89,0xcc,0x45,0x89,0xca,0x89,0xe8,0x41,0x1,0xe9,0x44,0x89,0xcd,0x1,0xc6,0x89,0x74,0x24,0x24,0xc1,0xe8,0x3,0x31,0xd0,0x8b,0x14,0x24,0x1,0xd3,0x48,0x89,0x5c,0x24,0x48,0x1,0xd0,0x89,0x44,0x24,0x10,0xc1,0xea,0x3,0x44,0x31,0xf2,0x8b,0x44,0x24,0x34,0x48,0x8b,0x5c,0x24,0x68,0x1,0xc3,0x1,0xc2,0x89,0x54,0x24,0x64,0xc1,0xe8,0x3,0x44,0x31,0xd8,0x44,0x8b,0x5c,0x24,0xc,0x44,0x1,0xd8]

set_option maxRecDepth 4096 in
theorem part13_bytes [Bindings] : part13.flatMap CheckedInstruction.bytes = part13Bytes  := by
  rfl

def part13Layout : List (BitVec 64 × Nat) :=
  [(0x1163c8, 3), (0x1163cb, 3), (0x1163ce, 2), (0x1163d0, 3), (0x1163d3, 3), (0x1163d6, 2), (0x1163d8, 5), (0x1163dd, 3), (0x1163e0, 3), (0x1163e3, 3), (0x1163e6, 3), (0x1163e9, 2), (0x1163eb, 3), (0x1163ee, 3), (0x1163f1, 2), (0x1163f3, 2), (0x1163f5, 4), (0x1163f9, 7), (0x116400, 7), (0x116407, 7), (0x11640e, 3), (0x116411, 4), (0x116415, 3), (0x116418, 7), (0x11641f, 4), (0x116423, 3), (0x116426, 4), (0x11642a, 7), (0x116431, 7), (0x116438, 7), (0x11643f, 3), (0x116442, 3), (0x116445, 4), (0x116449, 3), (0x11644c, 5), (0x116451, 3), (0x116454, 2), (0x116456, 5), (0x11645b, 3), (0x11645e, 3), (0x116461, 3), (0x116464, 2), (0x116466, 3), (0x116469, 3), (0x11646c, 2), (0x11646e, 4), (0x116472, 3), (0x116475, 2), (0x116477, 3), (0x11647a, 2), (0x11647c, 5), (0x116481, 2), (0x116483, 4), (0x116487, 3), (0x11648a, 3), (0x11648d, 4), (0x116491, 5), (0x116496, 2), (0x116498, 2), (0x11649a, 4), (0x11649e, 3), (0x1164a1, 3), (0x1164a4, 5), (0x1164a9, 3)]

theorem part13_layout [Bindings] : InstructionTrace.layout part13 = part13Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part13_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x163c8 228 = part13Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
