import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part42

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part43 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (ror_r64_one_effect_step 0x110681 0x49 0xce (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110684 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110687 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11068a 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11068e 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110691 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110694 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110697 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11069a 0x48 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11069e 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1106a1 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1106a6 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1106a9 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106ae 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1106b1 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106b5 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1106b8 0x48 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1106bc 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106bf 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1106c2 0x49 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1106c6 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1106ca 0x4d 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106cd 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1106d0 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1106d4 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1106d7 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1106da 0x48 (by simp [RexWPrefix]) 3 (.rip 0xefacf) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1106e1 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1106e4 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106e7 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1106ea 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1106ed 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1106f0 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106f3 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1106f6 0x49 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1106fa 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1106fd 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110700 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110704 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110707 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11070a 0x49 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11070e 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110711 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110714 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110717 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11071a 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11071d 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110720 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110723 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110726 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110729 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11072c 0x49 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110730 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110733 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110736 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11073a 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11073d 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110740 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110743 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110746 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110749 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11074c 0x49 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110750 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110753 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110756 0x49 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11075a 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11075d 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110762 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110765 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11076a 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11076d 0x49 0xea 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110771 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110774 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110777 0x48 0xc7 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11077b 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110780 0x4d 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110783 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110786 0x49 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11078a 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11078d 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110790 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110794 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110797 0x4c (by simp [RexWPrefix]) 10 (.rip 0xefa1a) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11079e 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107a1 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107a4 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107a7 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1107aa 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107ad 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107b0 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107b3 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1107b6 0x49 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1107ba 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107bd 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1107c0 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107c4 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107c7 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1107ca 0x49 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1107ce 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1107d1 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part43Bytes : List UInt8 :=
  [0x49,0xd1,0xce,0x4d,0x1,0xd9,0x4d,0x89,0xe3,0x49,0xc1,0xc3,0x38,0x49,0x31,0xda,0x4d,0x31,0xf3,0x4c,0x89,0xe3,0x4d,0x89,0xe6,0x48,0xc1,0xeb,0x7,0x4c,0x31,0xdb,0x4c,0x1,0x7c,0x24,0x48,0x4c,0x1,0xfb,0x48,0x89,0x5c,0x24,0x58,0x4d,0x89,0xfb,0x49,0xc1,0xeb,0x6,0x48,0x89,0xcb,0x48,0xc1,0xc3,0x32,0x4d,0x31,0xd3,0x49,0x89,0xca,0x49,0xc1,0xc2,0x2e,0x4c,0x8b,0x24,0x24,0x4d,0x1,0xdc,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x17,0x49,0x31,0xda,0x4d,0x31,0xd3,0x48,0x8b,0x1d,0xcf,0xfa,0xe,0x0,0x4c,0x1,0xe3,0x48,0x1,0xfb,0x48,0x89,0xef,0x4c,0x31,0xc7,0x48,0x21,0xcf,0x4c,0x31,0xc7,0x4d,0x89,0xca,0x49,0xc1,0xc2,0x24,0x48,0x1,0xfb,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x1e,0x4c,0x1,0xdb,0x4d,0x89,0xcb,0x49,0xc1,0xc3,0x19,0x4c,0x31,0xd7,0x49,0x31,0xfb,0x48,0x89,0xf7,0x48,0x21,0xd7,0x49,0x89,0xf7,0x49,0x31,0xd7,0x4d,0x21,0xcf,0x49,0x31,0xff,0x4d,0x1,0xdf,0x4d,0x89,0xf2,0x49,0xc1,0xc2,0x2d,0x48,0x1,0xd8,0x4c,0x89,0xf7,0x48,0xc1,0xc7,0x3,0x49,0x1,0xdf,0x4c,0x89,0xe3,0x4d,0x89,0xe3,0x49,0xd1,0xcb,0x4c,0x31,0xd7,0x4d,0x89,0xe2,0x49,0xc1,0xc2,0x38,0x4d,0x31,0xda,0x4d,0x89,0xe3,0x49,0xc1,0xeb,0x7,0x4d,0x31,0xd3,0x4c,0x1,0x74,0x24,0x68,0x4d,0x1,0xf3,0x4c,0x89,0x5c,0x24,0x60,0x4d,0x89,0xf2,0x49,0xc1,0xea,0x6,0x49,0x31,0xfa,0x48,0x89,0xc7,0x48,0xc1,0xc7,0x32,0x4c,0x8b,0x64,0x24,0x38,0x4d,0x1,0xd4,0x49,0x89,0xc2,0x49,0xc1,0xc2,0x2e,0x49,0x31,0xfa,0x48,0x89,0xc7,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xd7,0x4c,0x8b,0x15,0x1a,0xfa,0xe,0x0,0x4d,0x1,0xe2,0x4d,0x1,0xc2,0x49,0x89,0xc8,0x49,0x31,0xe8,0x49,0x21,0xc0,0x49,0x31,0xe8,0x4d,0x1,0xc2,0x4d,0x89,0xf8,0x49,0xc1,0xc0,0x24,0x49,0x1,0xfa,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x1e,0x4c,0x31,0xc7,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x19,0x49,0x31,0xfb,0x4c,0x89,0xcf]

set_option maxRecDepth 4096 in
theorem part43_bytes [Bindings] : part43.flatMap CheckedInstruction.bytes = part43Bytes := by
  rfl

def part43Layout : List (BitVec 64 × Nat) :=
  [(0x110681, 3), (0x110684, 3), (0x110687, 3), (0x11068a, 4), (0x11068e, 3), (0x110691, 3), (0x110694, 3), (0x110697, 3), (0x11069a, 4), (0x11069e, 3), (0x1106a1, 5), (0x1106a6, 3), (0x1106a9, 5), (0x1106ae, 3), (0x1106b1, 4), (0x1106b5, 3), (0x1106b8, 4), (0x1106bc, 3), (0x1106bf, 3), (0x1106c2, 4), (0x1106c6, 4), (0x1106ca, 3), (0x1106cd, 3), (0x1106d0, 4), (0x1106d4, 3), (0x1106d7, 3), (0x1106da, 7), (0x1106e1, 3), (0x1106e4, 3), (0x1106e7, 3), (0x1106ea, 3), (0x1106ed, 3), (0x1106f0, 3), (0x1106f3, 3), (0x1106f6, 4), (0x1106fa, 3), (0x1106fd, 3), (0x110700, 4), (0x110704, 3), (0x110707, 3), (0x11070a, 4), (0x11070e, 3), (0x110711, 3), (0x110714, 3), (0x110717, 3), (0x11071a, 3), (0x11071d, 3), (0x110720, 3), (0x110723, 3), (0x110726, 3), (0x110729, 3), (0x11072c, 4), (0x110730, 3), (0x110733, 3), (0x110736, 4), (0x11073a, 3), (0x11073d, 3), (0x110740, 3), (0x110743, 3), (0x110746, 3), (0x110749, 3), (0x11074c, 4), (0x110750, 3), (0x110753, 3), (0x110756, 4), (0x11075a, 3), (0x11075d, 5), (0x110762, 3), (0x110765, 5), (0x11076a, 3), (0x11076d, 4), (0x110771, 3), (0x110774, 3), (0x110777, 4), (0x11077b, 5), (0x110780, 3), (0x110783, 3), (0x110786, 4), (0x11078a, 3), (0x11078d, 3), (0x110790, 4), (0x110794, 3), (0x110797, 7), (0x11079e, 3), (0x1107a1, 3), (0x1107a4, 3), (0x1107a7, 3), (0x1107aa, 3), (0x1107ad, 3), (0x1107b0, 3), (0x1107b3, 3), (0x1107b6, 4), (0x1107ba, 3), (0x1107bd, 3), (0x1107c0, 4), (0x1107c4, 3), (0x1107c7, 3), (0x1107ca, 4), (0x1107ce, 3), (0x1107d1, 3)]

theorem part43_layout [Bindings] : InstructionTrace.layout part43 = part43Layout := by
  rfl

theorem part43_ordered [Bindings] : InstructionTrace.ordered 0x110681 part43 = true := by
  rw [InstructionTrace.ordered_eq_layout, part43_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part43_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10681 339 = part43Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
