import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part51

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part52 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111273 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111276 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111279 0x48 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11127d 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111280 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111283 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111286 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111289 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11128c 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11128f 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111292 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111295 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111298 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11129b 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11129f 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112a2 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1112a5 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112a9 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1112ac 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112b1 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1112b4 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112b8 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112bb 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1112be 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1112c2 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1112c7 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1112ca 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112cf 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1112d2 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112d6 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112d9 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1112dc 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112e0 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1112e3 0x48 (by simp [RexWPrefix]) 1 (.rip 0xeef56) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1112ea 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1112ed 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112f0 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112f3 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1112f6 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1112f9 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1112fc 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1112ff 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111302 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111306 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111309 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11130c 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111310 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111313 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111316 0x49 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11131a 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11131d 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111320 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111323 0x49 0xed (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111326 0x49 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111329 0x49 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11132c 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11132f 0x4d 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111332 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x111335 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11133a 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11133d 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111341 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111344 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111347 0x49 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11134b 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11134e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111353 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x111356 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111359 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11135c 0x49 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111360 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111363 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111367 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11136a 0x48 (by simp [RexWPrefix]) 0 (.rip 0xeeed7) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111371 0x4c (by simp [RexWPrefix]) 10 (.rip 0xeeed8) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111378 0x48 (by simp [RexWPrefix]) 6 (.rip 0xeeed9) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11137f 0x4c (by simp [RexWPrefix]) 15 (.rip 0xeeeda) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111386 0x4c (by simp [RexWPrefix]) 12 (.rip 0xeeedb) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11138d 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111392 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x111397 0x4c (by simp [RexWPrefix]) 12 (.rip 0xeeed2) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11139e 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1113a1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113a6 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1113a9 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1113ae 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1113b2 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1113b5 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113b9 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1113bc 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113c0 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1113c3 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113c7 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1113ca 0x49 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1113ce 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113d1 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1113d4 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1113d8 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113db 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113de 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part52Bytes : List UInt8 :=
  [0x48,0x31,0xf1,0x48,0x89,0xee,0x48,0xc1,0xc6,0x19,0x48,0x31,0xce,0x48,0x89,0xd9,0x4c,0x21,0xd9,0x48,0x89,0xdf,0x4c,0x31,0xdf,0x48,0x21,0xef,0x48,0x31,0xcf,0x48,0x1,0xf7,0x48,0x1,0xc2,0x4c,0x89,0xd1,0x48,0xc1,0xc1,0x2d,0x48,0x1,0xc7,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x3,0x48,0x31,0xc8,0x4c,0x1,0x54,0x24,0x40,0x4c,0x89,0xd1,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x48,0x89,0xd0,0x48,0xc1,0xc0,0x32,0x48,0x8b,0x74,0x24,0x8,0x48,0x1,0xce,0x48,0x89,0x74,0x24,0x8,0x48,0x89,0xd1,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xd0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x56,0xef,0xe,0x0,0x48,0x1,0xf1,0x4c,0x1,0xf9,0x4c,0x89,0xce,0x4c,0x31,0xf6,0x48,0x21,0xd6,0x4c,0x31,0xf6,0x48,0x1,0xf1,0x48,0x89,0xfe,0x48,0xc1,0xc6,0x24,0x48,0x1,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xf0,0x49,0x89,0xf8,0x49,0xc1,0xc0,0x19,0x49,0x31,0xc0,0x48,0x89,0xe8,0x48,0x21,0xd8,0x49,0x89,0xed,0x49,0x31,0xdd,0x49,0x21,0xfd,0x49,0x31,0xc5,0x4d,0x1,0xc5,0x49,0x1,0xcb,0x4c,0x89,0x64,0x24,0x38,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x2d,0x49,0x1,0xcd,0x4d,0x89,0xe0,0x49,0xc1,0xc0,0x3,0x49,0x31,0xc0,0x48,0x8b,0x4c,0x24,0x18,0x48,0x89,0xc8,0x48,0xd1,0xc8,0x49,0x89,0xca,0x49,0xc1,0xc2,0x38,0x49,0x31,0xc2,0x48,0xc1,0xe9,0x7,0x4c,0x31,0xd1,0x48,0x8b,0x5,0xd7,0xee,0xe,0x0,0x4c,0x8b,0x15,0xd8,0xee,0xe,0x0,0x48,0x8b,0x35,0xd9,0xee,0xe,0x0,0x4c,0x8b,0x3d,0xda,0xee,0xe,0x0,0x4c,0x8b,0x25,0xdb,0xee,0xe,0x0,0x4c,0x89,0x64,0x24,0x28,0x4c,0x8b,0x64,0x24,0x20,0x4c,0x3,0x25,0xd2,0xee,0xe,0x0,0x49,0x1,0xcc,0x48,0x8b,0x4c,0x24,0x38,0x49,0x1,0xcc,0x4c,0x89,0x64,0x24,0x20,0x48,0xc1,0xe9,0x6,0x4c,0x31,0xc1,0x4c,0x8b,0x24,0x24,0x49,0x1,0xcc,0x4c,0x89,0x24,0x24,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x32,0x4d,0x89,0xd8,0x49,0xc1,0xc0,0x2e,0x49,0x31,0xc8,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x17,0x4c,0x31,0xc1,0x4c,0x1,0xe0,0x4c,0x1,0xf0]

set_option maxRecDepth 4096 in
theorem part52_bytes [Bindings] : part52.flatMap CheckedInstruction.bytes = part52Bytes := by
  rfl

def part52Layout : List (BitVec 64 × Nat) :=
  [(0x111273, 3), (0x111276, 3), (0x111279, 4), (0x11127d, 3), (0x111280, 3), (0x111283, 3), (0x111286, 3), (0x111289, 3), (0x11128c, 3), (0x11128f, 3), (0x111292, 3), (0x111295, 3), (0x111298, 3), (0x11129b, 4), (0x11129f, 3), (0x1112a2, 3), (0x1112a5, 4), (0x1112a9, 3), (0x1112ac, 5), (0x1112b1, 3), (0x1112b4, 4), (0x1112b8, 3), (0x1112bb, 3), (0x1112be, 4), (0x1112c2, 5), (0x1112c7, 3), (0x1112ca, 5), (0x1112cf, 3), (0x1112d2, 4), (0x1112d6, 3), (0x1112d9, 3), (0x1112dc, 4), (0x1112e0, 3), (0x1112e3, 7), (0x1112ea, 3), (0x1112ed, 3), (0x1112f0, 3), (0x1112f3, 3), (0x1112f6, 3), (0x1112f9, 3), (0x1112fc, 3), (0x1112ff, 3), (0x111302, 4), (0x111306, 3), (0x111309, 3), (0x11130c, 4), (0x111310, 3), (0x111313, 3), (0x111316, 4), (0x11131a, 3), (0x11131d, 3), (0x111320, 3), (0x111323, 3), (0x111326, 3), (0x111329, 3), (0x11132c, 3), (0x11132f, 3), (0x111332, 3), (0x111335, 5), (0x11133a, 3), (0x11133d, 4), (0x111341, 3), (0x111344, 3), (0x111347, 4), (0x11134b, 3), (0x11134e, 5), (0x111353, 3), (0x111356, 3), (0x111359, 3), (0x11135c, 4), (0x111360, 3), (0x111363, 4), (0x111367, 3), (0x11136a, 7), (0x111371, 7), (0x111378, 7), (0x11137f, 7), (0x111386, 7), (0x11138d, 5), (0x111392, 5), (0x111397, 7), (0x11139e, 3), (0x1113a1, 5), (0x1113a6, 3), (0x1113a9, 5), (0x1113ae, 4), (0x1113b2, 3), (0x1113b5, 4), (0x1113b9, 3), (0x1113bc, 4), (0x1113c0, 3), (0x1113c3, 4), (0x1113c7, 3), (0x1113ca, 4), (0x1113ce, 3), (0x1113d1, 3), (0x1113d4, 4), (0x1113d8, 3), (0x1113db, 3), (0x1113de, 3)]

theorem part52_layout [Bindings] : InstructionTrace.layout part52 = part52Layout := by
  rfl

theorem part52_ordered [Bindings] : InstructionTrace.ordered 0x111273 part52 = true := by
  rw [InstructionTrace.ordered_eq_layout, part52_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part52_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x11273 366 = part52Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
