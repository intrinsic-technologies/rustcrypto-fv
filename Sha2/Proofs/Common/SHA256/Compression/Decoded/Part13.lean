import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part13 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf18 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf1b 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bf1e 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf20 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf23 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bf26 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bf28 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf2d 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf30 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf33 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bf36 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bf39 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf3b 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bf3e 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bf41 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bf43 0xf7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bf45 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf49 6 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf50 6 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf57 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bf5e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf61 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bf65 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf68 7 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10bf6f 0x41 0xed 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bf73 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bf76 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf7a 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf81 1 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf88 1 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bf8f 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bf92 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bf95 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bf99 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10bf9c 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bfa1 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bfa4 0xc6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bfa6 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bfab 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bfae 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bfb1 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bfb4 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bfb6 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bfb9 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bfbc 0xc6 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bfbe 6 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bfc2 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bfc5 0xd0 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bfc7 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bfca 0xd3 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10bfcc 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bfd1 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bfd3 0 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bfd7 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bfda 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bfdd 0 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bfe1 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bfe6 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bfe8 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bfea 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bfee 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bff1 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bff4 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bff9 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part13Bytes : List UInt8 :=
  [0x44,0x89,0xee,0xc1,0xc6,0x19,0x31,0xf8,0x44,0x89,0xe9,0xc1,0xc1,0xe,0x31,0xf1,0x4c,0x8b,0x44,0x24,0x50,0x44,0x89,0xc6,0xc1,0xc6,0x19,0x44,0x89,0xc7,0xc1,0xc7,0xe,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xee,0x3,0x31,0xfe,0x89,0xf7,0x8b,0x74,0x24,0x28,0x89,0xb4,0x24,0xa8,0x0,0x0,0x0,0x89,0xb4,0x24,0xac,0x0,0x0,0x0,0x89,0xb4,0x24,0xb0,0x0,0x0,0x0,0x44,0x1,0xee,0x89,0x74,0x24,0x28,0x44,0x1,0xef,0x89,0xbc,0x24,0x8c,0x0,0x0,0x0,0x41,0xc1,0xed,0x3,0x41,0x31,0xcd,0x8b,0x4c,0x24,0x40,0x89,0x8c,0x24,0x90,0x0,0x0,0x0,0x89,0x8c,0x24,0x94,0x0,0x0,0x0,0x89,0x8c,0x24,0x98,0x0,0x0,0x0,0x44,0x89,0xd6,0x44,0x1,0xd1,0x89,0x4c,0x24,0x40,0x45,0x1,0xd5,0x44,0x89,0x6c,0x24,0x4,0xc1,0xee,0x3,0x31,0xc6,0x44,0x8b,0x4c,0x24,0x24,0x44,0x89,0xc9,0x45,0x89,0xcc,0x45,0x89,0xca,0x89,0xe8,0x41,0x1,0xe9,0x44,0x89,0xcd,0x1,0xc6,0x89,0x74,0x24,0x24,0xc1,0xe8,0x3,0x31,0xd0,0x8b,0x14,0x24,0x1,0xd3,0x48,0x89,0x5c,0x24,0x48,0x1,0xd0,0x89,0x44,0x24,0x10,0xc1,0xea,0x3,0x44,0x31,0xf2,0x8b,0x44,0x24,0x34,0x48,0x8b,0x5c,0x24,0x68,0x1,0xc3,0x1,0xc2,0x89,0x54,0x24,0x64,0xc1,0xe8,0x3,0x44,0x31,0xd8,0x44,0x8b,0x5c,0x24,0xc,0x44,0x1,0xd8]

set_option maxRecDepth 4096 in
theorem part13_bytes [Bindings] : part13.flatMap CheckedInstruction.bytes = part13Bytes  := by
  rfl

def part13Layout : List (BitVec 64 × Nat) :=
  [(0x10bf18, 3), (0x10bf1b, 3), (0x10bf1e, 2), (0x10bf20, 3), (0x10bf23, 3), (0x10bf26, 2), (0x10bf28, 5), (0x10bf2d, 3), (0x10bf30, 3), (0x10bf33, 3), (0x10bf36, 3), (0x10bf39, 2), (0x10bf3b, 3), (0x10bf3e, 3), (0x10bf41, 2), (0x10bf43, 2), (0x10bf45, 4), (0x10bf49, 7), (0x10bf50, 7), (0x10bf57, 7), (0x10bf5e, 3), (0x10bf61, 4), (0x10bf65, 3), (0x10bf68, 7), (0x10bf6f, 4), (0x10bf73, 3), (0x10bf76, 4), (0x10bf7a, 7), (0x10bf81, 7), (0x10bf88, 7), (0x10bf8f, 3), (0x10bf92, 3), (0x10bf95, 4), (0x10bf99, 3), (0x10bf9c, 5), (0x10bfa1, 3), (0x10bfa4, 2), (0x10bfa6, 5), (0x10bfab, 3), (0x10bfae, 3), (0x10bfb1, 3), (0x10bfb4, 2), (0x10bfb6, 3), (0x10bfb9, 3), (0x10bfbc, 2), (0x10bfbe, 4), (0x10bfc2, 3), (0x10bfc5, 2), (0x10bfc7, 3), (0x10bfca, 2), (0x10bfcc, 5), (0x10bfd1, 2), (0x10bfd3, 4), (0x10bfd7, 3), (0x10bfda, 3), (0x10bfdd, 4), (0x10bfe1, 5), (0x10bfe6, 2), (0x10bfe8, 2), (0x10bfea, 4), (0x10bfee, 3), (0x10bff1, 3), (0x10bff4, 5), (0x10bff9, 3)]

theorem part13_layout [Bindings] : InstructionTrace.layout part13 = part13Layout := by
  rfl

theorem part13_ordered [Bindings] : InstructionTrace.ordered 0x10bf18 part13 = true := by
  rw [InstructionTrace.ordered_eq_layout, part13_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part13_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbf18 228 = part13Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
