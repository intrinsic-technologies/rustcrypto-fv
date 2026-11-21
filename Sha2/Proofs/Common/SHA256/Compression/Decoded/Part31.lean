import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part31 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cce6 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cce8 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cceb 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ccef 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ccf1 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ccf3 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ccf6 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ccf9 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ccfb 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ccfe 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cd01 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd05 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd08 0xde rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cd0a 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd0d 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10cd10 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cd17 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10cd19 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd1d 0xee rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cd1f 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cd22 0xd6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10cd24 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd29 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd2c 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd2e 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd31 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd33 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cd36 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd38 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd3a 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cd3d 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd3f 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd42 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10cd45 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd47 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd4a 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd4d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cd50 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd54 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd57 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd59 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd5c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10cd5f 0x41 0xc3 0x766a0abb (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd66 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd68 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd6b 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cd6e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd70 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cd73 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd76 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd78 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10cd7b 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd7d 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cd80 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd82 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cd85 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd89 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cd8c 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cd8e 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cd91 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd94 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cd97 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cd9b 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cd9e 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part31Bytes : List UInt8 :=
  [0x1,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x1,0xf0,0x89,0xea,0xc1,0xc2,0xd,0x44,0x31,0xca,0x89,0xde,0xc1,0xc6,0x19,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xe,0x41,0x31,0xf1,0x89,0xde,0xc1,0xee,0x3,0x44,0x31,0xce,0x1,0xac,0x24,0x80,0x0,0x0,0x0,0x1,0xee,0x89,0x74,0x24,0x50,0x89,0xee,0xc1,0xee,0xa,0x31,0xd6,0x44,0x8b,0x64,0x24,0x68,0x41,0x1,0xf4,0x89,0xca,0xc1,0xc2,0x1a,0x89,0xce,0xc1,0xc6,0x15,0x31,0xd6,0x89,0xca,0xc1,0xc2,0x7,0x31,0xf2,0x44,0x89,0xc6,0x44,0x31,0xee,0x21,0xce,0x44,0x31,0xee,0x45,0x1,0xe3,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x1e,0x41,0x1,0xf3,0x89,0xc6,0xc1,0xc6,0x13,0x41,0x1,0xd3,0x41,0x81,0xc3,0xbb,0xa,0x6a,0x76,0x89,0xc2,0xc1,0xc2,0xa,0x44,0x31,0xce,0x31,0xf2,0x41,0x89,0xf9,0x45,0x21,0xf1,0x89,0xfe,0x44,0x31,0xf6,0x21,0xc6,0x44,0x31,0xce,0x1,0xd6,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xf,0x45,0x1,0xda,0x89,0xda,0xc1,0xc2,0xd,0x44,0x1,0xde,0x45,0x89,0xe3,0x41,0xc1,0xc3,0x19,0x44,0x31,0xca,0x45,0x89,0xe1]

set_option maxRecDepth 4096 in
theorem part31_bytes [Bindings] : part31.flatMap CheckedInstruction.bytes = part31Bytes  := by
  rfl

def part31Layout : List (BitVec 64 × Nat) :=
  [(0x10cce6, 2), (0x10cce8, 3), (0x10cceb, 4), (0x10ccef, 2), (0x10ccf1, 2), (0x10ccf3, 3), (0x10ccf6, 3), (0x10ccf9, 2), (0x10ccfb, 3), (0x10ccfe, 3), (0x10cd01, 4), (0x10cd05, 3), (0x10cd08, 2), (0x10cd0a, 3), (0x10cd0d, 3), (0x10cd10, 7), (0x10cd17, 2), (0x10cd19, 4), (0x10cd1d, 2), (0x10cd1f, 3), (0x10cd22, 2), (0x10cd24, 5), (0x10cd29, 3), (0x10cd2c, 2), (0x10cd2e, 3), (0x10cd31, 2), (0x10cd33, 3), (0x10cd36, 2), (0x10cd38, 2), (0x10cd3a, 3), (0x10cd3d, 2), (0x10cd3f, 3), (0x10cd42, 3), (0x10cd45, 2), (0x10cd47, 3), (0x10cd4a, 3), (0x10cd4d, 3), (0x10cd50, 4), (0x10cd54, 3), (0x10cd57, 2), (0x10cd59, 3), (0x10cd5c, 3), (0x10cd5f, 7), (0x10cd66, 2), (0x10cd68, 3), (0x10cd6b, 3), (0x10cd6e, 2), (0x10cd70, 3), (0x10cd73, 3), (0x10cd76, 2), (0x10cd78, 3), (0x10cd7b, 2), (0x10cd7d, 3), (0x10cd80, 2), (0x10cd82, 3), (0x10cd85, 4), (0x10cd89, 3), (0x10cd8c, 2), (0x10cd8e, 3), (0x10cd91, 3), (0x10cd94, 3), (0x10cd97, 4), (0x10cd9b, 3), (0x10cd9e, 3)]

theorem part31_layout [Bindings] : InstructionTrace.layout part31 = part31Layout := by
  rfl

theorem part31_ordered [Bindings] : InstructionTrace.ordered 0x10cce6 part31 = true := by
  rw [InstructionTrace.ordered_eq_layout, part31_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part31_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcce6 187 = part31Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
