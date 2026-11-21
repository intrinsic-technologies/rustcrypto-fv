import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part31 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x117196 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117198 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11719b 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11719f 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171a1 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1171a3 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1171a6 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171a9 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1171ab 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1171ae 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1171b1 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1171b5 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171b8 0xde rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1171ba 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1171bd 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x1171c0 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1171c7 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1171c9 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171cd 0xee rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1171cf 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1171d2 0xd6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1171d4 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1171d9 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171dc 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1171de 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171e1 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1171e3 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1171e6 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1171e8 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1171ea 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1171ed 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1171ef 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1171f2 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1171f5 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1171f7 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1171fa 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1171fd 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117200 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117204 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117207 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117209 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11720c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x11720f 0x41 0xc3 0x766a0abb (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117216 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117218 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11721b 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11721e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117220 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117223 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117226 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117228 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x11722b 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11722d 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117230 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117232 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117235 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117239 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11723c 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11723e 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117241 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117244 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117247 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11724b 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11724e 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part31Bytes : List UInt8 :=
  [0x1,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x1,0xf0,0x89,0xea,0xc1,0xc2,0xd,0x44,0x31,0xca,0x89,0xde,0xc1,0xc6,0x19,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xe,0x41,0x31,0xf1,0x89,0xde,0xc1,0xee,0x3,0x44,0x31,0xce,0x1,0xac,0x24,0x80,0x0,0x0,0x0,0x1,0xee,0x89,0x74,0x24,0x50,0x89,0xee,0xc1,0xee,0xa,0x31,0xd6,0x44,0x8b,0x64,0x24,0x68,0x41,0x1,0xf4,0x89,0xca,0xc1,0xc2,0x1a,0x89,0xce,0xc1,0xc6,0x15,0x31,0xd6,0x89,0xca,0xc1,0xc2,0x7,0x31,0xf2,0x44,0x89,0xc6,0x44,0x31,0xee,0x21,0xce,0x44,0x31,0xee,0x45,0x1,0xe3,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x1e,0x41,0x1,0xf3,0x89,0xc6,0xc1,0xc6,0x13,0x41,0x1,0xd3,0x41,0x81,0xc3,0xbb,0xa,0x6a,0x76,0x89,0xc2,0xc1,0xc2,0xa,0x44,0x31,0xce,0x31,0xf2,0x41,0x89,0xf9,0x45,0x21,0xf1,0x89,0xfe,0x44,0x31,0xf6,0x21,0xc6,0x44,0x31,0xce,0x1,0xd6,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xf,0x45,0x1,0xda,0x89,0xda,0xc1,0xc2,0xd,0x44,0x1,0xde,0x45,0x89,0xe3,0x41,0xc1,0xc3,0x19,0x44,0x31,0xca,0x45,0x89,0xe1]

set_option maxRecDepth 4096 in
theorem part31_bytes [Bindings] : part31.flatMap CheckedInstruction.bytes = part31Bytes  := by
  rfl

def part31Layout : List (BitVec 64 × Nat) :=
  [(0x117196, 2), (0x117198, 3), (0x11719b, 4), (0x11719f, 2), (0x1171a1, 2), (0x1171a3, 3), (0x1171a6, 3), (0x1171a9, 2), (0x1171ab, 3), (0x1171ae, 3), (0x1171b1, 4), (0x1171b5, 3), (0x1171b8, 2), (0x1171ba, 3), (0x1171bd, 3), (0x1171c0, 7), (0x1171c7, 2), (0x1171c9, 4), (0x1171cd, 2), (0x1171cf, 3), (0x1171d2, 2), (0x1171d4, 5), (0x1171d9, 3), (0x1171dc, 2), (0x1171de, 3), (0x1171e1, 2), (0x1171e3, 3), (0x1171e6, 2), (0x1171e8, 2), (0x1171ea, 3), (0x1171ed, 2), (0x1171ef, 3), (0x1171f2, 3), (0x1171f5, 2), (0x1171f7, 3), (0x1171fa, 3), (0x1171fd, 3), (0x117200, 4), (0x117204, 3), (0x117207, 2), (0x117209, 3), (0x11720c, 3), (0x11720f, 7), (0x117216, 2), (0x117218, 3), (0x11721b, 3), (0x11721e, 2), (0x117220, 3), (0x117223, 3), (0x117226, 2), (0x117228, 3), (0x11722b, 2), (0x11722d, 3), (0x117230, 2), (0x117232, 3), (0x117235, 4), (0x117239, 3), (0x11723c, 2), (0x11723e, 3), (0x117241, 3), (0x117244, 3), (0x117247, 4), (0x11724b, 3), (0x11724e, 3)]

theorem part31_layout [Bindings] : InstructionTrace.layout part31 = part31Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part31_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17196 187 = part31Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
