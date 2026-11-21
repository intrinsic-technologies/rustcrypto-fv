import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part26

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part27 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f134 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f137 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f13b 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f13e 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f141 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f145 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f148 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f150 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f153 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f158 0x48 0xed 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f15c 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f15f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f167 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f16a 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f16d 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f171 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f174 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f178 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f17b 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f17e 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f182 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f185 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf0f3c) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f18c 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f18f 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f192 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f195 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f198 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f19b 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f19e 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f1a1 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1a4 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1a7 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1ab 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1ae 0x48 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1b2 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1b5 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1b8 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1bc 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1bf 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f1c2 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1c5 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1c8 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f1cb 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1ce 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1d1 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1d4 0x49 0xc6 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f1d8 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1db 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1de 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f1e2 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1e5 0x49 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f1e8 0x49 0xcd (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f1eb 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1ee 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f1f1 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1f5 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f1f8 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1fb 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f1fe 0x49 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f201 0x49 0xee 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f205 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f208 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 200)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f210 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f213 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f218 0x49 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f21c 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f21f 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f223 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f226 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f229 0x48 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f22d 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f235 0x4c 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f238 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f23b 0x49 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f23f 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f242 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f245 0x4c (by simp [RexWPrefix]) 15 (.rip 0xf0e84) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f24c 0x49 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f24f 0x4d 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f252 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f255 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f258 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f25b 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f25e 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f261 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f265 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f268 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f26b 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f26f 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f272 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f275 0x48 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f279 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f27c 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f27f 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f282 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f285 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f288 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f28b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f28e 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f291 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part27Bytes : List UInt8 :=
  [0x4c,0x89,0xfa,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x4c,0x89,0xf9,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x48,0x1,0xac,0x24,0x88,0x0,0x0,0x0,0x48,0x1,0xe9,0x48,0x89,0x4c,0x24,0x38,0x48,0xc1,0xed,0x6,0x48,0x31,0xc5,0x48,0x8b,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0x1,0xee,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0x15,0x3c,0xf,0xf,0x0,0x48,0x1,0xf2,0x4c,0x1,0xea,0x48,0x89,0xd9,0x4c,0x31,0xe1,0x48,0x21,0xf9,0x4c,0x31,0xe1,0x48,0x1,0xca,0x48,0x1,0xc2,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x1e,0x48,0x31,0xc1,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xc8,0x4d,0x89,0xd6,0x4d,0x21,0xce,0x4c,0x89,0xd1,0x4c,0x31,0xc9,0x4c,0x21,0xd9,0x4c,0x31,0xf1,0x4d,0x89,0xfe,0x49,0xc1,0xc6,0x2d,0x48,0x1,0xc1,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x3,0x49,0x1,0xd0,0x49,0x89,0xf5,0x49,0xd1,0xcd,0x48,0x1,0xd1,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x38,0x4c,0x31,0xf0,0x4c,0x31,0xea,0x49,0x89,0xf6,0x49,0x89,0xf5,0x49,0xc1,0xee,0x7,0x49,0x31,0xd6,0x4c,0x1,0xbc,0x24,0xc8,0x0,0x0,0x0,0x4d,0x1,0xfe,0x4c,0x89,0x74,0x24,0x68,0x49,0xc1,0xef,0x6,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x32,0x49,0x31,0xc7,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x2e,0x48,0x8b,0xac,0x24,0xa0,0x0,0x0,0x0,0x4c,0x1,0xfd,0x4d,0x89,0xc6,0x49,0xc1,0xc6,0x17,0x48,0x31,0xd0,0x49,0x31,0xc6,0x4c,0x8b,0x3d,0x84,0xe,0xf,0x0,0x49,0x1,0xef,0x4d,0x1,0xe7,0x48,0x89,0xf8,0x48,0x31,0xd8,0x4c,0x21,0xc0,0x48,0x31,0xd8,0x48,0x89,0xca,0x48,0xc1,0xc2,0x24,0x49,0x1,0xc7,0x48,0x89,0xc8,0x48,0xc1,0xc0,0x1e,0x4d,0x1,0xf7,0x48,0x89,0xce,0x48,0xc1,0xc6,0x19,0x48,0x31,0xd0,0x48,0x31,0xc6,0x4c,0x89,0xda,0x4c,0x21,0xd2,0x4c,0x89,0xd8,0x4c,0x31,0xd0,0x48,0x21,0xc8,0x48,0x31,0xd0,0x48,0x1,0xf0]

set_option maxRecDepth 4096 in
theorem part27_bytes [Bindings] : part27.flatMap CheckedInstruction.bytes = part27Bytes := by
  rfl

def part27Layout : List (BitVec 64 × Nat) :=
  [(0x10f134, 3), (0x10f137, 4), (0x10f13b, 3), (0x10f13e, 3), (0x10f141, 4), (0x10f145, 3), (0x10f148, 8), (0x10f150, 3), (0x10f153, 5), (0x10f158, 4), (0x10f15c, 3), (0x10f15f, 8), (0x10f167, 3), (0x10f16a, 3), (0x10f16d, 4), (0x10f171, 3), (0x10f174, 4), (0x10f178, 3), (0x10f17b, 3), (0x10f17e, 4), (0x10f182, 3), (0x10f185, 7), (0x10f18c, 3), (0x10f18f, 3), (0x10f192, 3), (0x10f195, 3), (0x10f198, 3), (0x10f19b, 3), (0x10f19e, 3), (0x10f1a1, 3), (0x10f1a4, 3), (0x10f1a7, 4), (0x10f1ab, 3), (0x10f1ae, 4), (0x10f1b2, 3), (0x10f1b5, 3), (0x10f1b8, 4), (0x10f1bc, 3), (0x10f1bf, 3), (0x10f1c2, 3), (0x10f1c5, 3), (0x10f1c8, 3), (0x10f1cb, 3), (0x10f1ce, 3), (0x10f1d1, 3), (0x10f1d4, 4), (0x10f1d8, 3), (0x10f1db, 3), (0x10f1de, 4), (0x10f1e2, 3), (0x10f1e5, 3), (0x10f1e8, 3), (0x10f1eb, 3), (0x10f1ee, 3), (0x10f1f1, 4), (0x10f1f5, 3), (0x10f1f8, 3), (0x10f1fb, 3), (0x10f1fe, 3), (0x10f201, 4), (0x10f205, 3), (0x10f208, 8), (0x10f210, 3), (0x10f213, 5), (0x10f218, 4), (0x10f21c, 3), (0x10f21f, 4), (0x10f223, 3), (0x10f226, 3), (0x10f229, 4), (0x10f22d, 8), (0x10f235, 3), (0x10f238, 3), (0x10f23b, 4), (0x10f23f, 3), (0x10f242, 3), (0x10f245, 7), (0x10f24c, 3), (0x10f24f, 3), (0x10f252, 3), (0x10f255, 3), (0x10f258, 3), (0x10f25b, 3), (0x10f25e, 3), (0x10f261, 4), (0x10f265, 3), (0x10f268, 3), (0x10f26b, 4), (0x10f26f, 3), (0x10f272, 3), (0x10f275, 4), (0x10f279, 3), (0x10f27c, 3), (0x10f27f, 3), (0x10f282, 3), (0x10f285, 3), (0x10f288, 3), (0x10f28b, 3), (0x10f28e, 3), (0x10f291, 3)]

theorem part27_layout [Bindings] : InstructionTrace.layout part27 = part27Layout := by
  rfl

theorem part27_ordered [Bindings] : InstructionTrace.ordered 0x10f134 part27 = true := by
  rw [InstructionTrace.ordered_eq_layout, part27_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part27_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf134 352 = part27Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
