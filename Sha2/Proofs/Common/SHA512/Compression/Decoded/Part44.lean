import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part43

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part44 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r64_r64_effect_step 0x1107d4 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107d7 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107da 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1107dd 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107e0 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107e3 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107e6 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107e9 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1107ec 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107f0 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107f3 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1107f6 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107fa 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107fd 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110800 0x49 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110803 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110806 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11080a 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11080d 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110810 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110814 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110817 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11081c 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11081f 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110827 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11082a 0x49 0xea 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11082e 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110831 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110836 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110839 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11083c 0x48 0xc7 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110840 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110843 0x49 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110847 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11084a 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11084d 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110851 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110854 0x4c (by simp [RexWPrefix]) 10 (.rip 0xef965) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11085b 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11085e 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110861 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110864 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110867 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11086a 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11086d 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110870 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110873 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110876 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11087a 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11087d 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110881 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110884 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110887 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11088b 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11088e 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110891 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110894 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110897 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11089a 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11089d 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1108a0 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1108a3 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1108a6 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108a9 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1108ac 0x49 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108b0 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1108b3 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1108b7 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108ba 0x4c 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108bd 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x1108c0 0x49 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108c3 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1108c6 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1108ca 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108cd 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1108d0 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1108d4 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1108d7 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1108dc 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1108df 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1108e4 0x49 0xec 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1108e8 0x49 0xfc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1108eb 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1108f0 0x4d 0xe5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108f3 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1108f6 0x48 0xc7 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1108fa 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1108fd 0x49 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110901 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110904 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110907 0x48 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11090b 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11090e 0x48 (by simp [RexWPrefix]) 7 (.rip 0xef8b3) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110915 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110918 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11091b 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11091e 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110921 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110924 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110927 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part44Bytes : List UInt8 :=
  [0x48,0x21,0xf7,0x4d,0x89,0xc8,0x49,0x31,0xf0,0x4d,0x21,0xf8,0x49,0x31,0xf8,0x4d,0x1,0xd8,0x4c,0x1,0xd2,0x49,0x89,0xdb,0x49,0xc1,0xc3,0x2d,0x4d,0x1,0xd0,0x48,0x89,0xdf,0x48,0xc1,0xc7,0x3,0x4c,0x31,0xdf,0x4d,0x89,0xe2,0x49,0xd1,0xca,0x4d,0x89,0xe3,0x49,0xc1,0xc3,0x38,0x4d,0x31,0xd3,0x4d,0x89,0xe2,0x49,0xc1,0xea,0x7,0x4d,0x31,0xda,0x48,0x1,0x5c,0x24,0x30,0x49,0x1,0xda,0x4c,0x89,0x94,0x24,0x90,0x0,0x0,0x0,0x49,0x89,0xda,0x49,0xc1,0xea,0x6,0x49,0x31,0xfa,0x4c,0x8b,0x74,0x24,0x70,0x4d,0x1,0xd6,0x48,0x89,0xd7,0x48,0xc1,0xc7,0x32,0x49,0x89,0xd2,0x49,0xc1,0xc2,0x2e,0x49,0x31,0xfa,0x48,0x89,0xd7,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xd7,0x4c,0x8b,0x15,0x65,0xf9,0xe,0x0,0x4d,0x1,0xf2,0x49,0x1,0xea,0x49,0x89,0xc3,0x49,0x31,0xcb,0x49,0x21,0xd3,0x49,0x31,0xcb,0x4d,0x1,0xda,0x49,0x1,0xfa,0x4c,0x89,0xc7,0x48,0xc1,0xc7,0x24,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x1e,0x49,0x31,0xfb,0x4c,0x89,0xc7,0x48,0xc1,0xc7,0x19,0x4c,0x31,0xdf,0x4c,0x89,0xfb,0x4c,0x21,0xcb,0x4d,0x89,0xfb,0x4d,0x31,0xcb,0x4d,0x21,0xc3,0x49,0x31,0xdb,0x49,0x1,0xfb,0x4c,0x1,0xd6,0x4d,0x1,0xd3,0x4d,0x89,0xe2,0x49,0xc1,0xc2,0x2d,0x4c,0x89,0xe7,0x48,0xc1,0xc7,0x3,0x4c,0x31,0xd7,0x4c,0x89,0xf5,0x4d,0x89,0xf2,0x49,0xd1,0xca,0x4c,0x89,0xf3,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xd3,0x4d,0x89,0xf2,0x49,0xc1,0xea,0x7,0x49,0x31,0xda,0x4c,0x1,0x64,0x24,0x20,0x4d,0x1,0xe2,0x4c,0x89,0x54,0x24,0x38,0x49,0xc1,0xec,0x6,0x49,0x31,0xfc,0x4c,0x8b,0x6c,0x24,0x40,0x4d,0x1,0xe5,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x32,0x49,0x89,0xf2,0x49,0xc1,0xc2,0x2e,0x49,0x31,0xfa,0x48,0x89,0xf3,0x48,0xc1,0xc3,0x17,0x4c,0x31,0xd3,0x48,0x8b,0x3d,0xb3,0xf8,0xe,0x0,0x4c,0x1,0xef,0x48,0x1,0xcf,0x48,0x89,0xd1,0x48,0x31,0xc1,0x48,0x21,0xf1,0x48,0x31,0xc1,0x48,0x1,0xcf]

set_option maxRecDepth 4096 in
theorem part44_bytes [Bindings] : part44.flatMap CheckedInstruction.bytes = part44Bytes := by
  rfl

def part44Layout : List (BitVec 64 × Nat) :=
  [(0x1107d4, 3), (0x1107d7, 3), (0x1107da, 3), (0x1107dd, 3), (0x1107e0, 3), (0x1107e3, 3), (0x1107e6, 3), (0x1107e9, 3), (0x1107ec, 4), (0x1107f0, 3), (0x1107f3, 3), (0x1107f6, 4), (0x1107fa, 3), (0x1107fd, 3), (0x110800, 3), (0x110803, 3), (0x110806, 4), (0x11080a, 3), (0x11080d, 3), (0x110810, 4), (0x110814, 3), (0x110817, 5), (0x11081c, 3), (0x11081f, 8), (0x110827, 3), (0x11082a, 4), (0x11082e, 3), (0x110831, 5), (0x110836, 3), (0x110839, 3), (0x11083c, 4), (0x110840, 3), (0x110843, 4), (0x110847, 3), (0x11084a, 3), (0x11084d, 4), (0x110851, 3), (0x110854, 7), (0x11085b, 3), (0x11085e, 3), (0x110861, 3), (0x110864, 3), (0x110867, 3), (0x11086a, 3), (0x11086d, 3), (0x110870, 3), (0x110873, 3), (0x110876, 4), (0x11087a, 3), (0x11087d, 4), (0x110881, 3), (0x110884, 3), (0x110887, 4), (0x11088b, 3), (0x11088e, 3), (0x110891, 3), (0x110894, 3), (0x110897, 3), (0x11089a, 3), (0x11089d, 3), (0x1108a0, 3), (0x1108a3, 3), (0x1108a6, 3), (0x1108a9, 3), (0x1108ac, 4), (0x1108b0, 3), (0x1108b3, 4), (0x1108b7, 3), (0x1108ba, 3), (0x1108bd, 3), (0x1108c0, 3), (0x1108c3, 3), (0x1108c6, 4), (0x1108ca, 3), (0x1108cd, 3), (0x1108d0, 4), (0x1108d4, 3), (0x1108d7, 5), (0x1108dc, 3), (0x1108df, 5), (0x1108e4, 4), (0x1108e8, 3), (0x1108eb, 5), (0x1108f0, 3), (0x1108f3, 3), (0x1108f6, 4), (0x1108fa, 3), (0x1108fd, 4), (0x110901, 3), (0x110904, 3), (0x110907, 4), (0x11090b, 3), (0x11090e, 7), (0x110915, 3), (0x110918, 3), (0x11091b, 3), (0x11091e, 3), (0x110921, 3), (0x110924, 3), (0x110927, 3)]

theorem part44_layout [Bindings] : InstructionTrace.layout part44 = part44Layout := by
  rfl

theorem part44_ordered [Bindings] : InstructionTrace.ordered 0x1107d4 part44 = true := by
  rw [InstructionTrace.ordered_eq_layout, part44_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part44_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x107d4 342 = part44Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
