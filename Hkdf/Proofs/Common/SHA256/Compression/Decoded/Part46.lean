import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part46 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b909 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b90c 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b90e 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b911 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b914 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b916 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b919 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b91c 0xc1 0x682e6ff3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b922 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b924 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b927 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b929 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b92b 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b92e 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b930 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b932 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b935 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b938 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b93b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b93e 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b941 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b944 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b947 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b949 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b94c 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b94f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b951 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b954 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b956 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b95a 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b95c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b95f 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b961 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b964 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b967 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b96b 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b96d 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b970 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b973 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b975 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b978 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b97b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b97d 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b980 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b983 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b986 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b989 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b98b 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10b98d 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b990 0xc2 0x748f82ee rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b996 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b999 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b99c 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b99f 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9a2 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9a4 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9a7 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9aa 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b9ac 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b9ae 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b9b0 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9b2 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b9b4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9b7 0xf9 rfl) (by x86_local)]

def part46Bytes : List UInt8 :=
  [0x44,0x21,0xd2,0x31,0xda,0x45,0x1,0xf0,0x41,0x1,0xd0,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xf3,0x6f,0x2e,0x68,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xd7,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xfa,0x89,0xc7,0x44,0x21,0xef,0x41,0x89,0xc0,0x45,0x31,0xe8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xc9,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x1,0x6c,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x68,0x1,0xd5,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xd2,0x44,0x31,0xda,0x44,0x21,0xca,0x44,0x31,0xda,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0xee,0x82,0x8f,0x74,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xfb,0x89,0xf7,0x21,0xc7,0x89,0xf1,0x31,0xc1,0x44,0x21,0xc1,0x31,0xf9]

set_option maxRecDepth 4096 in
theorem part46_bytes [Bindings] : part46.flatMap CheckedInstruction.bytes = part46Bytes  := by
  rfl

def part46Layout : List (BitVec 64 × Nat) :=
  [(0x10b909, 3), (0x10b90c, 2), (0x10b90e, 3), (0x10b911, 3), (0x10b914, 2), (0x10b916, 3), (0x10b919, 3), (0x10b91c, 6), (0x10b922, 2), (0x10b924, 3), (0x10b927, 2), (0x10b929, 2), (0x10b92b, 3), (0x10b92e, 2), (0x10b930, 2), (0x10b932, 3), (0x10b935, 3), (0x10b938, 3), (0x10b93b, 3), (0x10b93e, 3), (0x10b941, 3), (0x10b944, 3), (0x10b947, 2), (0x10b949, 3), (0x10b94c, 3), (0x10b94f, 2), (0x10b951, 3), (0x10b954, 2), (0x10b956, 4), (0x10b95a, 2), (0x10b95c, 3), (0x10b95f, 2), (0x10b961, 3), (0x10b964, 3), (0x10b967, 4), (0x10b96b, 2), (0x10b96d, 3), (0x10b970, 3), (0x10b973, 2), (0x10b975, 3), (0x10b978, 3), (0x10b97b, 2), (0x10b97d, 3), (0x10b980, 3), (0x10b983, 3), (0x10b986, 3), (0x10b989, 2), (0x10b98b, 2), (0x10b98d, 3), (0x10b990, 6), (0x10b996, 3), (0x10b999, 3), (0x10b99c, 3), (0x10b99f, 3), (0x10b9a2, 2), (0x10b9a4, 3), (0x10b9a7, 3), (0x10b9aa, 2), (0x10b9ac, 2), (0x10b9ae, 2), (0x10b9b0, 2), (0x10b9b2, 2), (0x10b9b4, 3), (0x10b9b7, 2)]

theorem part46_layout [Bindings] : InstructionTrace.layout part46 = part46Layout := by
  rfl

theorem part46_ordered [Bindings] : InstructionTrace.ordered 0x10b909 part46 = true := by
  rw [InstructionTrace.ordered_eq_layout, part46_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part46_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb909 176 = part46Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
