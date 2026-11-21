import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part12 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be34 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10be37 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10be3b 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10be40 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be43 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10be46 0x41 0xc4 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10be4a 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10be4c 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be50 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10be53 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10be57 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be59 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be5c 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10be5f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10be64 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be66 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10be6b 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be6f 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be71 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10be74 0xd5 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be76 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be7e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be80 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be83 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10be85 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10be87 2 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be8b 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10be8e 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be92 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be95 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10be97 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10be9a 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10be9d 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bea2 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bea5 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bea8 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10beab 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10beb3 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_effect_step 0x10beb7 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10bebc 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d32 180)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bec4 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bec7 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bec9 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10becc 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10becf 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 164)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bed7 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10beda 0x41 0xc6 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bede 0xcd rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bee0 5 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bee7 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10beeb 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10beed 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bef0 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bef3 2 (.sib 4 none 0 (.d32 156)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10befa 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10befc 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10beff 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bf02 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf07 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf0a 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bf0d 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf10 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf13 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bf16 0xca rfl) (by x86_local)]

def part12Bytes : List UInt8 :=
  [0x45,0x89,0xd3,0x41,0xc1,0xc3,0xf,0x44,0x89,0x5c,0x24,0x4,0x44,0x21,0xcd,0x45,0x89,0xd4,0x41,0xc1,0xc4,0xd,0x31,0xcd,0x8b,0x4c,0x24,0x60,0x41,0x89,0xca,0x41,0xc1,0xc2,0x19,0x1,0xf5,0xc1,0xc1,0xe,0x41,0x89,0xce,0x48,0x8b,0x4c,0x24,0x58,0x1,0xd1,0x48,0x89,0x4c,0x24,0x58,0x8b,0x74,0x24,0x8,0x89,0xf1,0xc1,0xc1,0x19,0x1,0xd5,0x48,0x89,0xac,0x24,0xd0,0x0,0x0,0x0,0x89,0xf2,0xc1,0xc2,0xe,0x89,0xd5,0x31,0xc7,0x8b,0x54,0x24,0xc,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x19,0xc1,0xc2,0xe,0x89,0xd8,0xc1,0xe8,0x3,0x41,0x89,0xc0,0x44,0x8b,0x5c,0x24,0x34,0x44,0x89,0xd8,0xc1,0xc0,0x19,0x41,0x31,0xf8,0x44,0x89,0x84,0x24,0xb8,0x0,0x0,0x0,0x41,0xc1,0xc3,0xe,0x44,0x33,0x64,0x24,0x4,0x44,0x89,0xa4,0x24,0xb4,0x0,0x0,0x0,0x8b,0x3c,0x24,0x89,0xfe,0xc1,0xc6,0x19,0x45,0x31,0xd6,0x44,0x89,0xb4,0x24,0xa4,0x0,0x0,0x0,0x41,0x89,0xfe,0x41,0xc1,0xc6,0xe,0x31,0xcd,0x89,0xac,0x24,0xa0,0x0,0x0,0x0,0x8b,0x6c,0x24,0x10,0x89,0xe9,0xc1,0xc1,0x19,0x44,0x31,0xca,0x89,0x94,0x24,0x9c,0x0,0x0,0x0,0x89,0xea,0xc1,0xc2,0xe,0x41,0x31,0xc3,0x44,0x8b,0x54,0x24,0x64,0x44,0x89,0xd7,0xc1,0xc7,0x19,0x41,0x31,0xf6,0x44,0x89,0xd0,0xc1,0xc0,0xe,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part12_bytes [Bindings] : part12.flatMap CheckedInstruction.bytes = part12Bytes  := by
  rfl

def part12Layout : List (BitVec 64 × Nat) :=
  [(0x10be34, 3), (0x10be37, 4), (0x10be3b, 5), (0x10be40, 3), (0x10be43, 3), (0x10be46, 4), (0x10be4a, 2), (0x10be4c, 4), (0x10be50, 3), (0x10be53, 4), (0x10be57, 2), (0x10be59, 3), (0x10be5c, 3), (0x10be5f, 5), (0x10be64, 2), (0x10be66, 5), (0x10be6b, 4), (0x10be6f, 2), (0x10be71, 3), (0x10be74, 2), (0x10be76, 8), (0x10be7e, 2), (0x10be80, 3), (0x10be83, 2), (0x10be85, 2), (0x10be87, 4), (0x10be8b, 3), (0x10be8e, 4), (0x10be92, 3), (0x10be95, 2), (0x10be97, 3), (0x10be9a, 3), (0x10be9d, 5), (0x10bea2, 3), (0x10bea5, 3), (0x10bea8, 3), (0x10beab, 8), (0x10beb3, 4), (0x10beb7, 5), (0x10bebc, 8), (0x10bec4, 3), (0x10bec7, 2), (0x10bec9, 3), (0x10becc, 3), (0x10becf, 8), (0x10bed7, 3), (0x10beda, 4), (0x10bede, 2), (0x10bee0, 7), (0x10bee7, 4), (0x10beeb, 2), (0x10beed, 3), (0x10bef0, 3), (0x10bef3, 7), (0x10befa, 2), (0x10befc, 3), (0x10beff, 3), (0x10bf02, 5), (0x10bf07, 3), (0x10bf0a, 3), (0x10bf0d, 3), (0x10bf10, 3), (0x10bf13, 3), (0x10bf16, 2)]

theorem part12_layout [Bindings] : InstructionTrace.layout part12 = part12Layout := by
  rfl

theorem part12_ordered [Bindings] : InstructionTrace.ordered 0x10be34 part12 = true := by
  rw [InstructionTrace.ordered_eq_layout, part12_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part12_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbe34 228 = part12Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
