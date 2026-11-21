import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part25

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part26 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10efe3 0x48 0xee 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10efe7 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efea 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10efed 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eff1 0x48 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eff4 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eff7 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10effb 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10effe 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f001 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f005 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f008 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf10a9) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f00f 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f012 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f015 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f018 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f01b 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f01e 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f021 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f024 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f027 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f02a 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f02e 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f031 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f034 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f038 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f03b 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f03e 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f042 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f045 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f048 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f04b 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f04e 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f051 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f054 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f057 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f05a 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f05d 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f060 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f064 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f067 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f06a 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f06e 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f071 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f074 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f077 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f07a 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f07e 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f081 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f084 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f088 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f08b 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f090 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f093 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f098 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f09b 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f09f 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f0a2 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 192)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f0aa 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0ad 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0b0 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0b4 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0b7 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0bb 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0be 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0c1 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0c5 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f0c8 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf0ff1) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f0cf 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f0d2 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0d5 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0d8 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f0db 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0de 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f0e1 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f0e4 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0e7 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0ea 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0ee 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0f1 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0f5 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f0f8 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f0fb 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f0ff 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f102 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f105 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f108 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f10b 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f10e 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f111 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f114 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f117 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f11a 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f11d 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f120 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f124 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f127 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f12b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f12e 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f131 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part26Bytes : List UInt8 :=
  [0x48,0xc1,0xee,0x6,0x48,0x31,0xc6,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x32,0x48,0x1,0xf5,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0xa9,0x10,0xf,0x0,0x48,0x1,0xe9,0x4c,0x1,0xf1,0x4c,0x89,0xea,0x4c,0x31,0xfa,0x4c,0x21,0xe2,0x4c,0x31,0xfa,0x4c,0x89,0xfe,0x48,0x1,0xd1,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x24,0x48,0x1,0xc1,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xd0,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x19,0x48,0x31,0xc2,0x4c,0x89,0xc0,0x48,0x21,0xf8,0x4d,0x89,0xc2,0x49,0x31,0xfa,0x4d,0x21,0xca,0x49,0x31,0xc2,0x49,0x1,0xd2,0x48,0x1,0xcb,0x4c,0x89,0xda,0x48,0xc1,0xc2,0x2d,0x49,0x1,0xca,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x3,0x48,0x31,0xd0,0x48,0x89,0xe9,0x48,0xd1,0xc9,0x48,0x89,0xea,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x48,0x89,0xe9,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x4c,0x1,0x5c,0x24,0x60,0x4c,0x1,0xd9,0x48,0x89,0x4c,0x24,0x20,0x4c,0x89,0xd9,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x4c,0x8b,0xbc,0x24,0xc0,0x0,0x0,0x0,0x49,0x1,0xcf,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xd9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0xf1,0xf,0xf,0x0,0x4c,0x1,0xf9,0x48,0x1,0xf1,0x4c,0x89,0xe2,0x4c,0x31,0xea,0x48,0x21,0xda,0x4c,0x31,0xea,0x48,0x1,0xd1,0x48,0x1,0xc1,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x4c,0x89,0xca,0x4c,0x21,0xc2,0x4d,0x89,0xcb,0x4d,0x31,0xc3,0x4d,0x21,0xd3,0x49,0x31,0xd3,0x49,0x1,0xc3,0x48,0x1,0xcf,0x49,0x1,0xcb,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x2d,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x3,0x48,0x31,0xc8,0x4c,0x89,0xf9,0x48,0xd1,0xc9]

set_option maxRecDepth 4096 in
theorem part26_bytes [Bindings] : part26.flatMap CheckedInstruction.bytes = part26Bytes := by
  rfl

def part26Layout : List (BitVec 64 × Nat) :=
  [(0x10efe3, 4), (0x10efe7, 3), (0x10efea, 3), (0x10efed, 4), (0x10eff1, 3), (0x10eff4, 3), (0x10eff7, 4), (0x10effb, 3), (0x10effe, 3), (0x10f001, 4), (0x10f005, 3), (0x10f008, 7), (0x10f00f, 3), (0x10f012, 3), (0x10f015, 3), (0x10f018, 3), (0x10f01b, 3), (0x10f01e, 3), (0x10f021, 3), (0x10f024, 3), (0x10f027, 3), (0x10f02a, 4), (0x10f02e, 3), (0x10f031, 3), (0x10f034, 4), (0x10f038, 3), (0x10f03b, 3), (0x10f03e, 4), (0x10f042, 3), (0x10f045, 3), (0x10f048, 3), (0x10f04b, 3), (0x10f04e, 3), (0x10f051, 3), (0x10f054, 3), (0x10f057, 3), (0x10f05a, 3), (0x10f05d, 3), (0x10f060, 4), (0x10f064, 3), (0x10f067, 3), (0x10f06a, 4), (0x10f06e, 3), (0x10f071, 3), (0x10f074, 3), (0x10f077, 3), (0x10f07a, 4), (0x10f07e, 3), (0x10f081, 3), (0x10f084, 4), (0x10f088, 3), (0x10f08b, 5), (0x10f090, 3), (0x10f093, 5), (0x10f098, 3), (0x10f09b, 4), (0x10f09f, 3), (0x10f0a2, 8), (0x10f0aa, 3), (0x10f0ad, 3), (0x10f0b0, 4), (0x10f0b4, 3), (0x10f0b7, 4), (0x10f0bb, 3), (0x10f0be, 3), (0x10f0c1, 4), (0x10f0c5, 3), (0x10f0c8, 7), (0x10f0cf, 3), (0x10f0d2, 3), (0x10f0d5, 3), (0x10f0d8, 3), (0x10f0db, 3), (0x10f0de, 3), (0x10f0e1, 3), (0x10f0e4, 3), (0x10f0e7, 3), (0x10f0ea, 4), (0x10f0ee, 3), (0x10f0f1, 4), (0x10f0f5, 3), (0x10f0f8, 3), (0x10f0fb, 4), (0x10f0ff, 3), (0x10f102, 3), (0x10f105, 3), (0x10f108, 3), (0x10f10b, 3), (0x10f10e, 3), (0x10f111, 3), (0x10f114, 3), (0x10f117, 3), (0x10f11a, 3), (0x10f11d, 3), (0x10f120, 4), (0x10f124, 3), (0x10f127, 4), (0x10f12b, 3), (0x10f12e, 3), (0x10f131, 3)]

theorem part26_layout [Bindings] : InstructionTrace.layout part26 = part26Layout := by
  rfl

theorem part26_ordered [Bindings] : InstructionTrace.ordered 0x10efe3 part26 = true := by
  rw [InstructionTrace.ordered_eq_layout, part26_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part26_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xefe3 337 = part26Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
