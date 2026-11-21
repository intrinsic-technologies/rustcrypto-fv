import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part24 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a8ca 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10a8cd 0xc1 0xc6e00bf3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8d3 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a8d6 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8d9 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8dc 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a8df 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8e3 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a8e6 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a8e8 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8eb 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8ee 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a8f1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8f4 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a8f7 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a8fa 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a8fd 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a8ff 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a902 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a905 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a907 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a90a 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a90c 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a90e 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a911 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a914 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a918 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a91b 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a91d 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a920 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a923 0 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a927 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a929 2 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a92d 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a92f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a932 0xca rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a934 0 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a938 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a93a 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a93d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a940 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a943 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a946 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a949 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a94b 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a94e 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a951 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a953 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a956 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a958 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a95b 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a95d 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a95f 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a962 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a966 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a968 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a96b 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a96e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10a970 0xc7 0xd5a79147 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a976 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a979 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a97c 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a97f 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a981 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part24Bytes : List UInt8 :=
  [0x44,0x1,0xe9,0x81,0xc1,0xf3,0xb,0xe0,0xc6,0x44,0x89,0xe2,0xc1,0xc2,0x13,0x44,0x31,0xca,0x45,0x89,0xe2,0x41,0xc1,0xc2,0xa,0x41,0x31,0xd2,0x89,0xf2,0x44,0x21,0xf2,0x41,0x89,0xf1,0x45,0x31,0xf1,0x45,0x21,0xe1,0x41,0x31,0xd1,0x45,0x1,0xd1,0x41,0x1,0xcf,0x89,0xc2,0xc1,0xc2,0xf,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0xd,0x31,0xd1,0x89,0xea,0xc1,0xc2,0x19,0x41,0x89,0xea,0x41,0xc1,0xc2,0xe,0x41,0x31,0xd2,0x89,0xea,0xc1,0xea,0x3,0x44,0x31,0xd2,0x1,0x44,0x24,0x38,0x1,0xc2,0x89,0x54,0x24,0x58,0x89,0xc2,0xc1,0xea,0xa,0x31,0xca,0x8b,0x44,0x24,0x24,0x1,0xd0,0x4d,0x89,0xfa,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xc2,0x31,0xda,0x44,0x21,0xd2,0x31,0xda,0x1,0xc7,0x45,0x89,0xca,0x41,0xc1,0xc2,0x1e,0x1,0xd7,0x44,0x89,0xca,0xc1,0xc2,0x13,0x1,0xcf,0x81,0xc7,0x47,0x91,0xa7,0xd5,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x44,0x31,0xd2,0x31,0xd1,0x44,0x89,0xe2]

set_option maxRecDepth 4096 in
theorem part24_bytes [Bindings] : part24.flatMap CheckedInstruction.bytes = part24Bytes  := by
  rfl

def part24Layout : List (BitVec 64 × Nat) :=
  [(0x10a8ca, 3), (0x10a8cd, 6), (0x10a8d3, 3), (0x10a8d6, 3), (0x10a8d9, 3), (0x10a8dc, 3), (0x10a8df, 4), (0x10a8e3, 3), (0x10a8e6, 2), (0x10a8e8, 3), (0x10a8eb, 3), (0x10a8ee, 3), (0x10a8f1, 3), (0x10a8f4, 3), (0x10a8f7, 3), (0x10a8fa, 3), (0x10a8fd, 2), (0x10a8ff, 3), (0x10a902, 3), (0x10a905, 2), (0x10a907, 3), (0x10a90a, 2), (0x10a90c, 2), (0x10a90e, 3), (0x10a911, 3), (0x10a914, 4), (0x10a918, 3), (0x10a91b, 2), (0x10a91d, 3), (0x10a920, 3), (0x10a923, 4), (0x10a927, 2), (0x10a929, 4), (0x10a92d, 2), (0x10a92f, 3), (0x10a932, 2), (0x10a934, 4), (0x10a938, 2), (0x10a93a, 3), (0x10a93d, 3), (0x10a940, 3), (0x10a943, 3), (0x10a946, 3), (0x10a949, 2), (0x10a94b, 3), (0x10a94e, 3), (0x10a951, 2), (0x10a953, 3), (0x10a956, 2), (0x10a958, 3), (0x10a95b, 2), (0x10a95d, 2), (0x10a95f, 3), (0x10a962, 4), (0x10a966, 2), (0x10a968, 3), (0x10a96b, 3), (0x10a96e, 2), (0x10a970, 6), (0x10a976, 3), (0x10a979, 3), (0x10a97c, 3), (0x10a97f, 2), (0x10a981, 3)]

theorem part24_layout [Bindings] : InstructionTrace.layout part24 = part24Layout := by
  rfl

theorem part24_ordered [Bindings] : InstructionTrace.ordered 0x10a8ca part24 = true := by
  rw [InstructionTrace.ordered_eq_layout, part24_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part24_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa8ca 186 = part24Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
