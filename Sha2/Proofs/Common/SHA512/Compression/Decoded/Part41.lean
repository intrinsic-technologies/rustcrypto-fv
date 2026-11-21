import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part40

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part41 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1103d9 0x49 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1103dd 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1103e2 0x4d 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103e5 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1103e8 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103ec 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103ef 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1103f2 0x48 (by simp [RexWPrefix]) 3 (.rip 0xefd97) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1103f9 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1103fc 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103ff 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110402 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110405 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110408 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11040b 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11040e 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110412 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110415 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110418 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11041c 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11041f 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110422 0x49 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110426 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110429 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11042c 0x49 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11042f 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110432 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110435 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110438 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11043b 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11043e 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110441 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110444 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110448 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11044b 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11044e 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110452 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110455 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110458 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11045b 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11045e 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110461 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110465 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110468 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11046b 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11046f 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110472 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110477 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11047a 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110482 0x49 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110486 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110489 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11048c 0x49 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110490 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110495 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110498 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11049b 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11049f 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104a2 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1104a5 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104a9 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1104ac 0x4c (by simp [RexWPrefix]) 11 (.rip 0xefce5) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104b3 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104b6 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104b9 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104bc 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1104bf 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104c2 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104c5 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104c8 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1104cb 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104cf 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104d2 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1104d5 0x49 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104d9 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104dc 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1104df 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104e3 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104e6 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1104e9 0x49 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104ec 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104ef 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1104f2 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1104f5 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104f8 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1104fb 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1104fe 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110501 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110505 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110508 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11050b 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11050f 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110512 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110515 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110518 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11051b 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11051f 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110522 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110525 0x49 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110529 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part41Bytes : List UInt8 :=
  [0x49,0xc1,0xc1,0x2e,0x4c,0x8b,0x6c,0x24,0x8,0x4d,0x1,0xdd,0x4d,0x89,0xf3,0x49,0xc1,0xc3,0x17,0x49,0x31,0xd9,0x4d,0x31,0xcb,0x48,0x8b,0x1d,0x97,0xfd,0xe,0x0,0x4c,0x1,0xeb,0x4c,0x1,0xd3,0x48,0x89,0xf0,0x48,0x31,0xd0,0x4c,0x21,0xf0,0x48,0x31,0xd0,0x49,0x89,0xc9,0x49,0xc1,0xc1,0x24,0x48,0x1,0xc3,0x48,0x89,0xc8,0x48,0xc1,0xc0,0x1e,0x4c,0x1,0xdb,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x19,0x4c,0x31,0xc8,0x49,0x31,0xc3,0x49,0x89,0xe9,0x4d,0x21,0xc1,0x48,0x89,0xe8,0x4c,0x31,0xc0,0x48,0x21,0xc8,0x4c,0x31,0xc8,0x4c,0x1,0xd8,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x2d,0x48,0x1,0xdf,0x4d,0x89,0xf9,0x49,0xc1,0xc1,0x3,0x48,0x1,0xd8,0x4c,0x89,0xeb,0x48,0xd1,0xcb,0x4d,0x31,0xd9,0x4d,0x89,0xeb,0x49,0xc1,0xc3,0x38,0x49,0x31,0xdb,0x4d,0x89,0xea,0x49,0xc1,0xea,0x7,0x4d,0x31,0xda,0x4c,0x1,0x7c,0x24,0x70,0x4d,0x1,0xfa,0x4c,0x89,0x94,0x24,0x80,0x0,0x0,0x0,0x49,0xc1,0xef,0x6,0x4d,0x31,0xcf,0x49,0x89,0xf9,0x49,0xc1,0xc1,0x32,0x4c,0x8b,0x54,0x24,0x28,0x4d,0x1,0xfa,0x49,0x89,0xfb,0x49,0xc1,0xc3,0x2e,0x4d,0x31,0xcb,0x49,0x89,0xf9,0x49,0xc1,0xc1,0x17,0x4d,0x31,0xd9,0x4c,0x8b,0x1d,0xe5,0xfc,0xe,0x0,0x4d,0x1,0xd3,0x49,0x1,0xd3,0x4c,0x89,0xf2,0x48,0x31,0xf2,0x48,0x21,0xfa,0x48,0x31,0xf2,0x49,0x1,0xd3,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x24,0x4d,0x1,0xcb,0x49,0x89,0xc1,0x49,0xc1,0xc1,0x1e,0x49,0x31,0xd1,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xcb,0x49,0x89,0xc9,0x49,0x21,0xe9,0x48,0x89,0xca,0x48,0x31,0xea,0x48,0x21,0xc2,0x4c,0x31,0xca,0x48,0x1,0xda,0x4d,0x1,0xd8,0x4c,0x89,0xeb,0x48,0xc1,0xc3,0x2d,0x4c,0x1,0xda,0x4d,0x89,0xe9,0x49,0xc1,0xc1,0x3,0x49,0x31,0xd9,0x4d,0x89,0xd3,0x49,0xd1,0xcb,0x4c,0x89,0xd3,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xdb,0x4d,0x89,0xd3,0x49,0xc1,0xeb,0x7,0x49,0x31,0xdb]

set_option maxRecDepth 4096 in
theorem part41_bytes [Bindings] : part41.flatMap CheckedInstruction.bytes = part41Bytes := by
  rfl

def part41Layout : List (BitVec 64 × Nat) :=
  [(0x1103d9, 4), (0x1103dd, 5), (0x1103e2, 3), (0x1103e5, 3), (0x1103e8, 4), (0x1103ec, 3), (0x1103ef, 3), (0x1103f2, 7), (0x1103f9, 3), (0x1103fc, 3), (0x1103ff, 3), (0x110402, 3), (0x110405, 3), (0x110408, 3), (0x11040b, 3), (0x11040e, 4), (0x110412, 3), (0x110415, 3), (0x110418, 4), (0x11041c, 3), (0x11041f, 3), (0x110422, 4), (0x110426, 3), (0x110429, 3), (0x11042c, 3), (0x11042f, 3), (0x110432, 3), (0x110435, 3), (0x110438, 3), (0x11043b, 3), (0x11043e, 3), (0x110441, 3), (0x110444, 4), (0x110448, 3), (0x11044b, 3), (0x11044e, 4), (0x110452, 3), (0x110455, 3), (0x110458, 3), (0x11045b, 3), (0x11045e, 3), (0x110461, 4), (0x110465, 3), (0x110468, 3), (0x11046b, 4), (0x11046f, 3), (0x110472, 5), (0x110477, 3), (0x11047a, 8), (0x110482, 4), (0x110486, 3), (0x110489, 3), (0x11048c, 4), (0x110490, 5), (0x110495, 3), (0x110498, 3), (0x11049b, 4), (0x11049f, 3), (0x1104a2, 3), (0x1104a5, 4), (0x1104a9, 3), (0x1104ac, 7), (0x1104b3, 3), (0x1104b6, 3), (0x1104b9, 3), (0x1104bc, 3), (0x1104bf, 3), (0x1104c2, 3), (0x1104c5, 3), (0x1104c8, 3), (0x1104cb, 4), (0x1104cf, 3), (0x1104d2, 3), (0x1104d5, 4), (0x1104d9, 3), (0x1104dc, 3), (0x1104df, 4), (0x1104e3, 3), (0x1104e6, 3), (0x1104e9, 3), (0x1104ec, 3), (0x1104ef, 3), (0x1104f2, 3), (0x1104f5, 3), (0x1104f8, 3), (0x1104fb, 3), (0x1104fe, 3), (0x110501, 4), (0x110505, 3), (0x110508, 3), (0x11050b, 4), (0x11050f, 3), (0x110512, 3), (0x110515, 3), (0x110518, 3), (0x11051b, 4), (0x11051f, 3), (0x110522, 3), (0x110525, 4), (0x110529, 3)]

theorem part41_layout [Bindings] : InstructionTrace.layout part41 = part41Layout := by
  rfl

theorem part41_ordered [Bindings] : InstructionTrace.ordered 0x1103d9 part41 = true := by
  rw [InstructionTrace.ordered_eq_layout, part41_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part41_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x103d9 339 = part41Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
