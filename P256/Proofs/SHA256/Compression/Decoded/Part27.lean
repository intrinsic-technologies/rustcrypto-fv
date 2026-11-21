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

def part27 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116ebe 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116ec0 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116ec4 0xea rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116ec6 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116eca 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116ecc 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116ecf 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x116ed1 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116ed6 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ed9 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116edc 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116edf 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ee2 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116ee5 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ee7 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116eea 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116eed 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116eef 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ef1 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116ef4 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ef7 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116efa 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116efd 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116eff 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f02 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116f05 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x116f07 0x27b70a85) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f0c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f0f 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f12 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f14 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f17 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f1a 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f1c 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116f1f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f22 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116f25 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116f28 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f2b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116f2d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116f2f 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f32 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f35 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116f38 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f3a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f3d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f40 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f42 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f45 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f48 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f4b 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f4e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f50 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116f53 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f56 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x116f58 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116f5d 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116f60 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f64 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116f67 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f6a 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116f6c 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116f70 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f72 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part27Bytes : List UInt8 :=
  [0x31,0xfa,0x1,0x6c,0x24,0x68,0x1,0xea,0x89,0x54,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x8b,0x7c,0x24,0xc,0x41,0x1,0xd7,0x44,0x89,0xe1,0xc1,0xc1,0x1a,0x44,0x89,0xe2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xe1,0xc1,0xc1,0x7,0x31,0xd1,0x89,0xf2,0x44,0x31,0xf2,0x44,0x21,0xe2,0x44,0x31,0xf2,0x44,0x1,0xf8,0x1,0xd0,0x44,0x89,0xc2,0xc1,0xc2,0x1e,0x1,0xc8,0x5,0x85,0xa,0xb7,0x27,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xd1,0x44,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xca,0x44,0x89,0xef,0x44,0x21,0xdf,0x44,0x89,0xe9,0x44,0x31,0xd9,0x44,0x21,0xc1,0x31,0xf9,0x1,0xd1,0x41,0x1,0xc1,0x44,0x89,0xd2,0xc1,0xc2,0xf,0x1,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0xd,0x31,0xd0,0x44,0x89,0xfa,0xc1,0xc2,0x19,0x44,0x89,0xff,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xfa,0xc1,0xea,0x3,0x31,0xfa,0x44,0x1,0x54,0x24,0x14,0x44,0x1,0xd2,0x89,0x54,0x24,0x40,0x44,0x89,0xd2,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x6c,0x24,0x8,0x1,0xd5,0x44,0x89,0xc8]

set_option maxRecDepth 4096 in
theorem part27_bytes [Bindings] : part27.flatMap CheckedInstruction.bytes = part27Bytes  := by
  rfl

def part27Layout : List (BitVec 64 × Nat) :=
  [(0x116ebe, 2), (0x116ec0, 4), (0x116ec4, 2), (0x116ec6, 4), (0x116eca, 2), (0x116ecc, 3), (0x116ecf, 2), (0x116ed1, 5), (0x116ed6, 3), (0x116ed9, 3), (0x116edc, 3), (0x116edf, 3), (0x116ee2, 3), (0x116ee5, 2), (0x116ee7, 3), (0x116eea, 3), (0x116eed, 2), (0x116eef, 2), (0x116ef1, 3), (0x116ef4, 3), (0x116ef7, 3), (0x116efa, 3), (0x116efd, 2), (0x116eff, 3), (0x116f02, 3), (0x116f05, 2), (0x116f07, 5), (0x116f0c, 3), (0x116f0f, 3), (0x116f12, 2), (0x116f14, 3), (0x116f17, 3), (0x116f1a, 2), (0x116f1c, 3), (0x116f1f, 3), (0x116f22, 3), (0x116f25, 3), (0x116f28, 3), (0x116f2b, 2), (0x116f2d, 2), (0x116f2f, 3), (0x116f32, 3), (0x116f35, 3), (0x116f38, 2), (0x116f3a, 3), (0x116f3d, 3), (0x116f40, 2), (0x116f42, 3), (0x116f45, 3), (0x116f48, 3), (0x116f4b, 3), (0x116f4e, 2), (0x116f50, 3), (0x116f53, 3), (0x116f56, 2), (0x116f58, 5), (0x116f5d, 3), (0x116f60, 4), (0x116f64, 3), (0x116f67, 3), (0x116f6a, 2), (0x116f6c, 4), (0x116f70, 2), (0x116f72, 3)]

theorem part27_layout [Bindings] : InstructionTrace.layout part27 = part27Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part27_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16ebe 183 = part27Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
