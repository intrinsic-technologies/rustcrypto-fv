import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part45 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c25 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c27 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c2a 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117c2c 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117c31 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c34 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117c36 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c39 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c3b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c3e 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117c41 5 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117c45 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c47 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c4a 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c4d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c4f 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c52 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c55 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c57 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117c59 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117c5c 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117c5f 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117c62 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117c65 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x117c68 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117c6c 0xc1 0x5b9cca4f rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c72 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c74 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c77 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c79 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c7c 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c7e 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c80 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c83 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c85 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117c88 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c8b 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117c8e 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117c91 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c93 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117c95 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117c97 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117c9a 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c9c 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c9f 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ca2 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ca5 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117ca8 0xca rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x117caa 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117cae 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117cb1 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cb4 0xd1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117cb6 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117cbb 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117cbe 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117cc1 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117cc4 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117cc7 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cca 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ccc 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ccf 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cd2 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117cd4 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cd7 0xda rfl) (by x86_local)]

def part45Bytes : List UInt8 :=
  [0x89,0xea,0xc1,0xc2,0xd,0x31,0xca,0x44,0x8b,0x64,0x24,0x10,0x41,0x1,0xec,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x48,0x1,0xcd,0x44,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x7,0x31,0xca,0x89,0xd9,0x44,0x31,0xc1,0x44,0x21,0xd9,0x44,0x31,0xc1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x32,0x81,0xc1,0x4f,0xca,0x9c,0x5b,0x89,0xc2,0xc1,0xc2,0x1e,0x89,0xc6,0xc1,0xc6,0x13,0x31,0xd6,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xef,0x44,0x21,0xcf,0x44,0x89,0xee,0x44,0x31,0xce,0x21,0xc6,0x31,0xfe,0x1,0xd6,0x41,0x1,0xca,0x1,0xce,0x44,0x89,0xf9,0xc1,0xc1,0xf,0x44,0x89,0xfa,0xc1,0xc2,0xd,0x31,0xca,0x44,0x1,0x3c,0x24,0x44,0x89,0xf9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x8b,0x74,0x24,0x70,0x41,0x1,0xce,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xda,0x31,0xda]

set_option maxRecDepth 4096 in
theorem part45_bytes [Bindings] : part45.flatMap CheckedInstruction.bytes = part45Bytes  := by
  rfl

def part45Layout : List (BitVec 64 × Nat) :=
  [(0x117c25, 2), (0x117c27, 3), (0x117c2a, 2), (0x117c2c, 5), (0x117c31, 3), (0x117c34, 2), (0x117c36, 3), (0x117c39, 2), (0x117c3b, 3), (0x117c3e, 3), (0x117c41, 4), (0x117c45, 2), (0x117c47, 3), (0x117c4a, 3), (0x117c4d, 2), (0x117c4f, 3), (0x117c52, 3), (0x117c55, 2), (0x117c57, 2), (0x117c59, 3), (0x117c5c, 3), (0x117c5f, 3), (0x117c62, 3), (0x117c65, 3), (0x117c68, 4), (0x117c6c, 6), (0x117c72, 2), (0x117c74, 3), (0x117c77, 2), (0x117c79, 3), (0x117c7c, 2), (0x117c7e, 2), (0x117c80, 3), (0x117c83, 2), (0x117c85, 3), (0x117c88, 3), (0x117c8b, 3), (0x117c8e, 3), (0x117c91, 2), (0x117c93, 2), (0x117c95, 2), (0x117c97, 3), (0x117c9a, 2), (0x117c9c, 3), (0x117c9f, 3), (0x117ca2, 3), (0x117ca5, 3), (0x117ca8, 2), (0x117caa, 4), (0x117cae, 3), (0x117cb1, 3), (0x117cb4, 2), (0x117cb6, 5), (0x117cbb, 3), (0x117cbe, 3), (0x117cc1, 3), (0x117cc4, 3), (0x117cc7, 3), (0x117cca, 2), (0x117ccc, 3), (0x117ccf, 3), (0x117cd2, 2), (0x117cd4, 3), (0x117cd7, 2)]

theorem part45_layout [Bindings] : InstructionTrace.layout part45 = part45Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part45_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17c25 180 = part45Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
