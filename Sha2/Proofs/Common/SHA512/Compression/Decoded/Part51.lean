import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part50

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part51 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r64_r64_effect_step 0x11111c 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11111f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111122 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111125 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111128 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11112b 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11112f 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111132 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111136 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111139 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11113c 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111140 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111143 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111146 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111149 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11114c 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11114f 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111152 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111155 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111158 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11115b 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11115e 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111161 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111165 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111168 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11116c 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11116f 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111174 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111177 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11117b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11117e 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x111186 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11118b 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11118e 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111191 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111195 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111198 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11119c 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11119f 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1111a2 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111a6 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1111a9 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef080) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111b0 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111b3 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111b6 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111b9 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1111bc 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111bf 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111c2 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111c5 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111c8 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1111cb 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111cf 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1111d2 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111d6 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111d9 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1111dc 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111e0 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111e3 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1111e6 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111e9 0x4c 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111ec 0x48 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1111ef 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1111f2 0x48 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111f5 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111f8 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1111fb 0x48 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1111fe 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111201 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111205 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111208 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11120c 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11120f 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111214 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111217 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11121b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11121e 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x111223 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111228 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11122b 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11122f 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111232 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111235 0x48 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111239 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11123c 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11123f 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111243 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111246 0x48 (by simp [RexWPrefix]) 0 (.rip 0xeefeb) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11124d 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111250 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111253 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111256 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111259 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11125c 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11125f 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111262 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111265 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111269 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11126c 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11126f 0x48 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part51Bytes : List UInt8 :=
  [0x4c,0x21,0xff,0x48,0x31,0xf7,0x48,0x1,0xf9,0x48,0x1,0xc1,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xdf,0x48,0xc1,0xc7,0x1e,0x48,0x31,0xc7,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xf8,0x48,0x89,0xd7,0x4c,0x21,0xcf,0x48,0x89,0xd3,0x4c,0x31,0xcb,0x4c,0x21,0xdb,0x48,0x31,0xfb,0x48,0x1,0xc3,0x49,0x1,0xce,0x48,0x1,0xcb,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x2d,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1,0x4c,0x1,0x64,0x24,0x48,0x4c,0x89,0xe0,0x48,0xc1,0xe8,0x6,0x48,0x31,0xc8,0x4c,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x4c,0x3,0x54,0x24,0x18,0x49,0x1,0xc2,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x32,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x80,0xf0,0xe,0x0,0x4c,0x1,0xd1,0x48,0x1,0xf1,0x4c,0x89,0xfe,0x4c,0x31,0xc6,0x4c,0x21,0xf6,0x4c,0x31,0xc6,0x48,0x1,0xf1,0x48,0x1,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x24,0x48,0x89,0xde,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xc6,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xf0,0x4c,0x89,0xde,0x48,0x21,0xd6,0x4c,0x89,0xdd,0x48,0x31,0xd5,0x48,0x21,0xdd,0x48,0x31,0xf5,0x48,0x1,0xc5,0x49,0x1,0xc9,0x48,0x1,0xcd,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x2d,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1,0x4c,0x1,0x6c,0x24,0x30,0x4c,0x89,0xe8,0x48,0xc1,0xe8,0x6,0x48,0x31,0xc8,0x4c,0x8b,0x64,0x24,0x38,0x4c,0x3,0x64,0x24,0x10,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x32,0x49,0x1,0xc4,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x2e,0x48,0x31,0xc8,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x17,0x48,0x31,0xc1,0x48,0x8b,0x5,0xeb,0xef,0xe,0x0,0x4c,0x1,0xe0,0x4c,0x1,0xc0,0x4c,0x89,0xf6,0x4c,0x31,0xfe,0x4c,0x21,0xce,0x4c,0x31,0xfe,0x48,0x1,0xf0,0x48,0x89,0xee,0x48,0xc1,0xc6,0x24,0x48,0x1,0xc8,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x1e]

set_option maxRecDepth 4096 in
theorem part51_bytes [Bindings] : part51.flatMap CheckedInstruction.bytes = part51Bytes := by
  rfl

def part51Layout : List (BitVec 64 × Nat) :=
  [(0x11111c, 3), (0x11111f, 3), (0x111122, 3), (0x111125, 3), (0x111128, 3), (0x11112b, 4), (0x11112f, 3), (0x111132, 4), (0x111136, 3), (0x111139, 3), (0x11113c, 4), (0x111140, 3), (0x111143, 3), (0x111146, 3), (0x111149, 3), (0x11114c, 3), (0x11114f, 3), (0x111152, 3), (0x111155, 3), (0x111158, 3), (0x11115b, 3), (0x11115e, 3), (0x111161, 4), (0x111165, 3), (0x111168, 4), (0x11116c, 3), (0x11116f, 5), (0x111174, 3), (0x111177, 4), (0x11117b, 3), (0x11117e, 8), (0x111186, 5), (0x11118b, 3), (0x11118e, 3), (0x111191, 4), (0x111195, 3), (0x111198, 4), (0x11119c, 3), (0x11119f, 3), (0x1111a2, 4), (0x1111a6, 3), (0x1111a9, 7), (0x1111b0, 3), (0x1111b3, 3), (0x1111b6, 3), (0x1111b9, 3), (0x1111bc, 3), (0x1111bf, 3), (0x1111c2, 3), (0x1111c5, 3), (0x1111c8, 3), (0x1111cb, 4), (0x1111cf, 3), (0x1111d2, 4), (0x1111d6, 3), (0x1111d9, 3), (0x1111dc, 4), (0x1111e0, 3), (0x1111e3, 3), (0x1111e6, 3), (0x1111e9, 3), (0x1111ec, 3), (0x1111ef, 3), (0x1111f2, 3), (0x1111f5, 3), (0x1111f8, 3), (0x1111fb, 3), (0x1111fe, 3), (0x111201, 4), (0x111205, 3), (0x111208, 4), (0x11120c, 3), (0x11120f, 5), (0x111214, 3), (0x111217, 4), (0x11121b, 3), (0x11121e, 5), (0x111223, 5), (0x111228, 3), (0x11122b, 4), (0x11122f, 3), (0x111232, 3), (0x111235, 4), (0x111239, 3), (0x11123c, 3), (0x11123f, 4), (0x111243, 3), (0x111246, 7), (0x11124d, 3), (0x111250, 3), (0x111253, 3), (0x111256, 3), (0x111259, 3), (0x11125c, 3), (0x11125f, 3), (0x111262, 3), (0x111265, 4), (0x111269, 3), (0x11126c, 3), (0x11126f, 4)]

theorem part51_layout [Bindings] : InstructionTrace.layout part51 = part51Layout := by
  rfl

theorem part51_ordered [Bindings] : InstructionTrace.ordered 0x11111c part51 = true := by
  rw [InstructionTrace.ordered_eq_layout, part51_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part51_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x1111c 343 = part51Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
