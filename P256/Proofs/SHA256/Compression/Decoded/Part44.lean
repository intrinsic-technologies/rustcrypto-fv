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

def part44 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_eax_imm32_effect_step 0x117b70 0x391c0cb3) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b75 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b78 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b7b 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b7e 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b81 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b83 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b86 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b89 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b8b 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117b8e 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b91 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b94 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117b97 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b9a 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b9d 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117ba0 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ba2 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117ba5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ba7 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117baa 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117bac 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117baf 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117bb1 7 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117bb5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117bb7 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117bba 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117bbc 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117bc1 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117bc4 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117bc6 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117bc9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117bcb 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117bce 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117bd0 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117bd2 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117bd5 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117bd7 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117bda 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117bdd 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117bdf 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117be2 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117be5 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117be8 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117beb 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x117bee 0x42 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117bf2 0xc2 0x4ed8aa4a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117bf8 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117bfb 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117bfe 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c00 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c03 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c06 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c08 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117c0b 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117c0e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117c11 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117c14 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117c17 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117c19 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117c1b 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117c1e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117c20 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117c23 0xd0 rfl) (by x86_local)]

def part44Bytes : List UInt8 :=
  [0x5,0xb3,0xc,0x1c,0x39,0x44,0x89,0xc9,0xc1,0xc1,0x1e,0x44,0x89,0xca,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xd2,0x44,0x21,0xda,0x45,0x89,0xd5,0x45,0x31,0xdd,0x45,0x21,0xcd,0x41,0x31,0xd5,0x41,0x1,0xcd,0x1,0xc3,0x41,0x1,0xc5,0x89,0xf8,0xc1,0xc0,0xf,0x89,0xf9,0xc1,0xc1,0xd,0x31,0xc1,0x1,0x7c,0x24,0x58,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x44,0x8b,0x7c,0x24,0x14,0x41,0x1,0xc7,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x31,0xf1,0x21,0xd9,0x44,0x31,0xf1,0x45,0x1,0xfc,0x41,0x1,0xcc,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x42,0x8d,0x14,0x20,0x81,0xc2,0x4a,0xaa,0xd8,0x4e,0x44,0x89,0xe8,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xc1,0x44,0x89,0xce,0x44,0x21,0xd6,0x44,0x89,0xc8,0x44,0x31,0xd0,0x44,0x21,0xe8,0x31,0xf0,0x1,0xc8,0x41,0x1,0xd3,0x89,0xe9,0xc1,0xc1,0xf,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part44_bytes [Bindings] : part44.flatMap CheckedInstruction.bytes = part44Bytes  := by
  rfl

def part44Layout : List (BitVec 64 × Nat) :=
  [(0x117b70, 5), (0x117b75, 3), (0x117b78, 3), (0x117b7b, 3), (0x117b7e, 3), (0x117b81, 2), (0x117b83, 3), (0x117b86, 3), (0x117b89, 2), (0x117b8b, 3), (0x117b8e, 3), (0x117b91, 3), (0x117b94, 3), (0x117b97, 3), (0x117b9a, 3), (0x117b9d, 3), (0x117ba0, 2), (0x117ba2, 3), (0x117ba5, 2), (0x117ba7, 3), (0x117baa, 2), (0x117bac, 3), (0x117baf, 2), (0x117bb1, 4), (0x117bb5, 2), (0x117bb7, 3), (0x117bba, 2), (0x117bbc, 5), (0x117bc1, 3), (0x117bc4, 2), (0x117bc6, 3), (0x117bc9, 2), (0x117bcb, 3), (0x117bce, 2), (0x117bd0, 2), (0x117bd2, 3), (0x117bd5, 2), (0x117bd7, 3), (0x117bda, 3), (0x117bdd, 2), (0x117bdf, 3), (0x117be2, 3), (0x117be5, 3), (0x117be8, 3), (0x117beb, 3), (0x117bee, 4), (0x117bf2, 6), (0x117bf8, 3), (0x117bfb, 3), (0x117bfe, 2), (0x117c00, 3), (0x117c03, 3), (0x117c06, 2), (0x117c08, 3), (0x117c0b, 3), (0x117c0e, 3), (0x117c11, 3), (0x117c14, 3), (0x117c17, 2), (0x117c19, 2), (0x117c1b, 3), (0x117c1e, 2), (0x117c20, 3), (0x117c23, 2)]

theorem part44_layout [Bindings] : InstructionTrace.layout part44 = part44Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part44_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17b70 181 = part44Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
