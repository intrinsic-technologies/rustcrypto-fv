import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part05 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b930 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b933 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b936 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b93a 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b93c 0xc2 0xab1c5ed5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b942 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b945 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b948 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b94b 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b94e 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b951 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b953 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b956 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b959 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b95c 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b95f 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b962 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b965 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b968 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b96a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b96c 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b96f 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b972 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b974 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b977 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b979 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b97b 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b97e 0xd3 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b980 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b985 5 (.base 2 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b988 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b98a 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b98e 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b990 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b992 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b994 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b996 0xfa rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10b998 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b99a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b99c 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10b99e 2 (.sib 3 (some 0) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b9a1 0xc2 0xd807aa98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9a7 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9aa 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9ad 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9b0 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9b3 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9b5 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9b8 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9bb 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9bd 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b9c0 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9c3 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b9c6 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b9c9 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9cc 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b9ce 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b9d0 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b9d3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9d5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9d8 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9db 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9de 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9e1 0xd3 rfl) (by x86_local)]

def part05Bytes : List UInt8 :=
  [0x44,0x1,0xd3,0x45,0x89,0xda,0x41,0xc1,0xc2,0x1e,0x1,0xda,0x81,0xc2,0xd5,0x5e,0x1c,0xab,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xd3,0x44,0x89,0xdd,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xc3,0x44,0x21,0xcb,0x45,0x89,0xc2,0x45,0x31,0xca,0x45,0x21,0xda,0x41,0x31,0xda,0x41,0x1,0xea,0x1,0xd7,0x89,0xfb,0xc1,0xc3,0x1a,0x41,0x1,0xd2,0x89,0xfa,0xc1,0xc2,0x15,0x31,0xda,0x89,0xfb,0xc1,0xc3,0x7,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x20,0xf,0xcd,0x89,0x6c,0x24,0x60,0x89,0xfa,0x21,0xf2,0x1,0xe8,0x1,0xd0,0x89,0xfa,0xf7,0xd2,0x21,0xca,0x1,0xd0,0x8d,0x14,0x3,0x81,0xc2,0x98,0xaa,0x7,0xd8,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xc3,0x44,0x89,0xd5,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xdb,0x44,0x21,0xc3,0x44,0x89,0xd8,0x44,0x31,0xc0,0x44,0x21,0xd0,0x31,0xd8,0x1,0xe8,0x41,0x1,0xd1,0x1,0xd0,0x44,0x89,0xca,0xc1,0xc2,0x1a,0x44,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xd3]

set_option maxRecDepth 4096 in
theorem part05_bytes [Bindings] : part05.flatMap CheckedInstruction.bytes = part05Bytes  := by
  rfl

def part05Layout : List (BitVec 64 × Nat) :=
  [(0x10b930, 3), (0x10b933, 3), (0x10b936, 4), (0x10b93a, 2), (0x10b93c, 6), (0x10b942, 3), (0x10b945, 3), (0x10b948, 3), (0x10b94b, 3), (0x10b94e, 3), (0x10b951, 2), (0x10b953, 3), (0x10b956, 3), (0x10b959, 3), (0x10b95c, 3), (0x10b95f, 3), (0x10b962, 3), (0x10b965, 3), (0x10b968, 2), (0x10b96a, 2), (0x10b96c, 3), (0x10b96f, 3), (0x10b972, 2), (0x10b974, 3), (0x10b977, 2), (0x10b979, 2), (0x10b97b, 3), (0x10b97e, 2), (0x10b980, 5), (0x10b985, 3), (0x10b988, 2), (0x10b98a, 4), (0x10b98e, 2), (0x10b990, 2), (0x10b992, 2), (0x10b994, 2), (0x10b996, 2), (0x10b998, 2), (0x10b99a, 2), (0x10b99c, 2), (0x10b99e, 3), (0x10b9a1, 6), (0x10b9a7, 3), (0x10b9aa, 3), (0x10b9ad, 3), (0x10b9b0, 3), (0x10b9b3, 2), (0x10b9b5, 3), (0x10b9b8, 3), (0x10b9bb, 2), (0x10b9bd, 3), (0x10b9c0, 3), (0x10b9c3, 3), (0x10b9c6, 3), (0x10b9c9, 3), (0x10b9cc, 2), (0x10b9ce, 2), (0x10b9d0, 3), (0x10b9d3, 2), (0x10b9d5, 3), (0x10b9d8, 3), (0x10b9db, 3), (0x10b9de, 3), (0x10b9e1, 2)]

theorem part05_layout [Bindings] : InstructionTrace.layout part05 = part05Layout := by
  rfl

theorem part05_ordered [Bindings] : InstructionTrace.ordered 0x10b930 part05 = true := by
  rw [InstructionTrace.ordered_eq_layout, part05_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part05_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb930 179 = part05Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
