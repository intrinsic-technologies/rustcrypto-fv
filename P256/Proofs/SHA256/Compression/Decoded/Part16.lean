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

def part16 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116661 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116664 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116667 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116669 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11666c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x116671 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116673 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116676 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116679 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11667c 0x41 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11667f 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116682 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116687 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11668a 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11668d 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116694 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116697 0 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11669e 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166a1 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1166a3 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1166ab 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1166af 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1166b2 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166b4 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1166b7 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166b9 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166bc 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166be 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166c1 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166c4 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166c7 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166ca 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166cc 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1166cf 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166d2 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x1166d4 6 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1166d7 0xf1 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1166d9 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1166dd 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1166df 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166e2 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1166e4 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1166e7 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1166e9 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166ec 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166ef 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166f2 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166f5 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1166f8 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1166fa 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1166fd 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116700 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116702 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116705 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116708 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11670b 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11670e 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116710 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116713 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116716 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116718 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11671b 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11671e 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x116720 0x2de92c6f) (by x86_local)]

def part16Bytes : List UInt8 :=
  [0x44,0x89,0xf9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xca,0x48,0x8b,0x5c,0x24,0x70,0x21,0xda,0x45,0x89,0xcc,0x41,0x31,0xdc,0x45,0x21,0xfc,0x41,0x31,0xd4,0x41,0x1,0xcc,0x4c,0x8b,0x6c,0x24,0x78,0x41,0x1,0xc5,0x41,0x1,0xc4,0x8b,0x8c,0x24,0x90,0x0,0x0,0x0,0xc1,0xc1,0x19,0x8b,0x84,0x24,0x94,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x44,0x8b,0x94,0x24,0x98,0x0,0x0,0x0,0x41,0xc1,0xea,0x3,0x41,0x31,0xc2,0x89,0xf1,0xc1,0xc1,0xf,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0x19,0x44,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xca,0x44,0x89,0xc1,0xc1,0xe9,0x3,0x31,0xd1,0x1,0x34,0x24,0x1,0xf1,0x89,0x4c,0x24,0x38,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x1,0xd5,0x1,0xcd,0x4d,0x89,0xea,0x44,0x89,0xd0,0xc1,0xc0,0x1a,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xd9,0x44,0x21,0xd1,0x44,0x31,0xd9,0x1,0xef,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x1,0xcf,0x44,0x89,0xe1,0xc1,0xc1,0x13,0x1,0xf8,0x5,0x6f,0x2c,0xe9,0x2d]

set_option maxRecDepth 4096 in
theorem part16_bytes [Bindings] : part16.flatMap CheckedInstruction.bytes = part16Bytes  := by
  rfl

def part16Layout : List (BitVec 64 × Nat) :=
  [(0x116661, 3), (0x116664, 3), (0x116667, 2), (0x116669, 3), (0x11666c, 5), (0x116671, 2), (0x116673, 3), (0x116676, 3), (0x116679, 3), (0x11667c, 3), (0x11667f, 3), (0x116682, 5), (0x116687, 3), (0x11668a, 3), (0x11668d, 7), (0x116694, 3), (0x116697, 7), (0x11669e, 3), (0x1166a1, 2), (0x1166a3, 8), (0x1166ab, 4), (0x1166af, 3), (0x1166b2, 2), (0x1166b4, 3), (0x1166b7, 2), (0x1166b9, 3), (0x1166bc, 2), (0x1166be, 3), (0x1166c1, 3), (0x1166c4, 3), (0x1166c7, 3), (0x1166ca, 2), (0x1166cc, 3), (0x1166cf, 3), (0x1166d2, 2), (0x1166d4, 3), (0x1166d7, 2), (0x1166d9, 4), (0x1166dd, 2), (0x1166df, 3), (0x1166e2, 2), (0x1166e4, 3), (0x1166e7, 2), (0x1166e9, 3), (0x1166ec, 3), (0x1166ef, 3), (0x1166f2, 3), (0x1166f5, 3), (0x1166f8, 2), (0x1166fa, 3), (0x1166fd, 3), (0x116700, 2), (0x116702, 3), (0x116705, 3), (0x116708, 3), (0x11670b, 3), (0x11670e, 2), (0x116710, 3), (0x116713, 3), (0x116716, 2), (0x116718, 3), (0x11671b, 3), (0x11671e, 2), (0x116720, 5)]

theorem part16_layout [Bindings] : InstructionTrace.layout part16 = part16Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part16_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16661 196 = part16Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
