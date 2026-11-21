import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part31

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part32 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f7e3 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f7e8 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f7eb 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7f3 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f7f6 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7fa 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f7fd 0x49 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f801 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f804 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f807 0x48 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f80b 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f80f 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f812 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f815 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f819 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f81c 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f81f 0x4c (by simp [RexWPrefix]) 8 (.rip 0xf08ea) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f826 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f829 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f82c 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f82f 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f832 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f835 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f838 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f83b 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f83f 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f842 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f845 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f849 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f84c 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f84f 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f853 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f856 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f859 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f85c 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f85f 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f862 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f865 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f868 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f86b 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f86e 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f871 0x48 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f875 0x4d 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f878 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f87b 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f87f 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f882 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f885 0x49 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f888 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f88b 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f88e 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f892 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f895 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f898 0x49 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f89c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f89f 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8a4 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f8a7 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8ac 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f8af 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f8b3 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8b6 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f8b9 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f8bd 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8c2 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8c5 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f8c8 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f8cc 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8cf 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f8d2 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f8d6 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f8d9 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf0838) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8e0 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8e3 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8e6 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f8e9 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f8ec 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f8ef 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8f2 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8f5 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f8f8 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f8fc 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f8ff 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f902 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f906 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f909 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f90c 0x49 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f910 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f913 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f916 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f919 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f91c 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f91f 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f922 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f925 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f928 0x49 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f92b 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f92e 0x49 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f932 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f935 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part32Bytes : List UInt8 :=
  [0x4c,0x1,0x5c,0x24,0x38,0x4d,0x1,0xd8,0x4c,0x89,0x84,0x24,0x80,0x0,0x0,0x0,0x4c,0x89,0xdf,0x48,0xc1,0xef,0x6,0x4d,0x89,0xf8,0x49,0xc1,0xc0,0x32,0x48,0x31,0xf7,0x4c,0x89,0xfe,0x48,0xc1,0xc6,0x2e,0x4c,0x8b,0x14,0x24,0x49,0x1,0xfa,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xc6,0x48,0x31,0xf7,0x4c,0x8b,0x5,0xea,0x8,0xf,0x0,0x4d,0x1,0xd0,0x49,0x1,0xc0,0x48,0x89,0xd8,0x48,0x31,0xd0,0x4c,0x21,0xf8,0x48,0x31,0xd0,0x48,0x89,0xce,0x48,0xc1,0xc6,0x24,0x49,0x1,0xc0,0x48,0x89,0xc8,0x48,0xc1,0xc0,0x1e,0x49,0x1,0xf8,0x48,0x89,0xcf,0x48,0xc1,0xc7,0x19,0x48,0x31,0xf0,0x48,0x31,0xc7,0x48,0x89,0xee,0x4c,0x21,0xee,0x48,0x89,0xe8,0x4c,0x31,0xe8,0x48,0x21,0xc8,0x48,0x31,0xf0,0x48,0x1,0xf8,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x2d,0x4d,0x1,0xc4,0x4c,0x89,0xce,0x48,0xc1,0xc6,0x3,0x4c,0x1,0xc0,0x4d,0x89,0xd0,0x49,0xd1,0xc8,0x48,0x31,0xfe,0x4c,0x89,0xd7,0x48,0xc1,0xc7,0x38,0x4c,0x31,0xc7,0x4d,0x89,0xd0,0x49,0xc1,0xe8,0x7,0x49,0x31,0xf8,0x4c,0x1,0x4c,0x24,0x68,0x4d,0x1,0xc8,0x4c,0x89,0x44,0x24,0x58,0x4c,0x89,0xcf,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x4c,0x89,0xe6,0x48,0xc1,0xc6,0x32,0x4c,0x8b,0x4c,0x24,0x48,0x49,0x1,0xf9,0x4c,0x89,0xe7,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x4c,0x89,0xe6,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x38,0x8,0xf,0x0,0x4c,0x1,0xcf,0x48,0x1,0xd7,0x4c,0x89,0xfa,0x48,0x31,0xda,0x4c,0x21,0xe2,0x48,0x31,0xda,0x48,0x1,0xd7,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x24,0x48,0x1,0xf7,0x48,0x89,0xc6,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xd6,0x49,0x89,0xc0,0x49,0xc1,0xc0,0x19,0x49,0x31,0xf0,0x48,0x89,0xce,0x48,0x21,0xee,0x48,0x89,0xca,0x48,0x31,0xea,0x48,0x21,0xc2,0x48,0x31,0xf2,0x4c,0x1,0xc2,0x49,0x1,0xfd,0x4d,0x89,0xd0,0x49,0xc1,0xc0,0x2d,0x48,0x1,0xfa,0x4c,0x89,0xd6]

set_option maxRecDepth 4096 in
theorem part32_bytes [Bindings] : part32.flatMap CheckedInstruction.bytes = part32Bytes := by
  rfl

def part32Layout : List (BitVec 64 × Nat) :=
  [(0x10f7e3, 5), (0x10f7e8, 3), (0x10f7eb, 8), (0x10f7f3, 3), (0x10f7f6, 4), (0x10f7fa, 3), (0x10f7fd, 4), (0x10f801, 3), (0x10f804, 3), (0x10f807, 4), (0x10f80b, 4), (0x10f80f, 3), (0x10f812, 3), (0x10f815, 4), (0x10f819, 3), (0x10f81c, 3), (0x10f81f, 7), (0x10f826, 3), (0x10f829, 3), (0x10f82c, 3), (0x10f82f, 3), (0x10f832, 3), (0x10f835, 3), (0x10f838, 3), (0x10f83b, 4), (0x10f83f, 3), (0x10f842, 3), (0x10f845, 4), (0x10f849, 3), (0x10f84c, 3), (0x10f84f, 4), (0x10f853, 3), (0x10f856, 3), (0x10f859, 3), (0x10f85c, 3), (0x10f85f, 3), (0x10f862, 3), (0x10f865, 3), (0x10f868, 3), (0x10f86b, 3), (0x10f86e, 3), (0x10f871, 4), (0x10f875, 3), (0x10f878, 3), (0x10f87b, 4), (0x10f87f, 3), (0x10f882, 3), (0x10f885, 3), (0x10f888, 3), (0x10f88b, 3), (0x10f88e, 4), (0x10f892, 3), (0x10f895, 3), (0x10f898, 4), (0x10f89c, 3), (0x10f89f, 5), (0x10f8a4, 3), (0x10f8a7, 5), (0x10f8ac, 3), (0x10f8af, 4), (0x10f8b3, 3), (0x10f8b6, 3), (0x10f8b9, 4), (0x10f8bd, 5), (0x10f8c2, 3), (0x10f8c5, 3), (0x10f8c8, 4), (0x10f8cc, 3), (0x10f8cf, 3), (0x10f8d2, 4), (0x10f8d6, 3), (0x10f8d9, 7), (0x10f8e0, 3), (0x10f8e3, 3), (0x10f8e6, 3), (0x10f8e9, 3), (0x10f8ec, 3), (0x10f8ef, 3), (0x10f8f2, 3), (0x10f8f5, 3), (0x10f8f8, 4), (0x10f8fc, 3), (0x10f8ff, 3), (0x10f902, 4), (0x10f906, 3), (0x10f909, 3), (0x10f90c, 4), (0x10f910, 3), (0x10f913, 3), (0x10f916, 3), (0x10f919, 3), (0x10f91c, 3), (0x10f91f, 3), (0x10f922, 3), (0x10f925, 3), (0x10f928, 3), (0x10f92b, 3), (0x10f92e, 4), (0x10f932, 3), (0x10f935, 3)]

theorem part32_layout [Bindings] : InstructionTrace.layout part32 = part32Layout := by
  rfl

theorem part32_ordered [Bindings] : InstructionTrace.ordered 0x10f7e3 part32 = true := by
  rw [InstructionTrace.ordered_eq_layout, part32_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part32_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf7e3 341 = part32Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
