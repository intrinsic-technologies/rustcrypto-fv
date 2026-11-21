import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part54

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part55 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11167c 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111680 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111683 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111686 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111689 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11168c 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11168f 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111697 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11169a 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11169d 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1116a0 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116a3 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1116a6 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1116a9 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1116ac 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116b1 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1116b4 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1116b8 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116bb 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1116be 0x48 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116c2 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116c5 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1116c8 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1116cc 0x48 0xee 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116d0 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1116d3 0x49 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116d7 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116da 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116dd 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1116e0 0x48 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116e4 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116e7 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1116ea 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1116ef 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1116f2 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1116f5 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116f8 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1116fb 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1116fe 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111701 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111704 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111707 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11170b 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11170e 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111711 0x48 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111715 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111718 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11171b 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11171f 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111722 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111725 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111728 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11172b 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11172e 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111731 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111735 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111738 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11173b 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11173f 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111742 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111745 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111749 0x49 0xec 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11174d 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111750 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111754 0x4d 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111757 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11175a 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11175e 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111761 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111764 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11176c 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111771 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111774 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111777 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11177a 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11177d 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111780 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111783 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111786 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111789 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11178d 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111790 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111793 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111796 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11179a 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11179d 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1117a0 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1117a4 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1117a7 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1117aa 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1117ad 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1117b0 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1117b3 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1117b6 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117b9 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 304)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1117c1 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117c4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 312)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117cc 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 328)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117d4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1117dc 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 360)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
  ]

def part55Bytes : List UInt8 :=
  [0x48,0xc1,0xc3,0x19,0x48,0x31,0xd3,0x49,0x89,0xc3,0x4d,0x21,0xf3,0x48,0x89,0xc1,0x4c,0x31,0xf1,0x4c,0x1,0xb4,0x24,0xb0,0x0,0x0,0x0,0x4d,0x89,0xf2,0x4d,0x21,0xce,0x4d,0x31,0xca,0x49,0x21,0xc2,0x4d,0x31,0xf2,0x49,0x1,0xda,0x4d,0x1,0xf8,0x48,0x8b,0x74,0x24,0x30,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x2d,0x4d,0x1,0xfa,0x48,0x89,0xf3,0x48,0xc1,0xc3,0x3,0x48,0x31,0xd3,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x32,0x48,0xc1,0xee,0x6,0x4d,0x89,0xc6,0x49,0xc1,0xc6,0x2e,0x48,0x31,0xde,0x49,0x89,0xf7,0x4c,0x89,0xc3,0x48,0xc1,0xc3,0x17,0x49,0x31,0xd6,0x4c,0x31,0xf3,0x48,0x8b,0x74,0x24,0x20,0x4c,0x1,0xfe,0x48,0x1,0xee,0x4c,0x89,0xea,0x48,0x31,0xfa,0x4c,0x21,0xc2,0x48,0x31,0xfa,0x48,0x1,0xd6,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x24,0x48,0x1,0xde,0x4c,0x89,0xd3,0x48,0xc1,0xc3,0x1e,0x48,0x31,0xd3,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x19,0x48,0x31,0xda,0x4c,0x21,0xd1,0x4c,0x31,0xd9,0x48,0x1,0xd1,0x49,0x1,0xf1,0x4c,0x89,0xe2,0x48,0xc1,0xc2,0x2d,0x48,0x1,0xf1,0x4d,0x89,0xe3,0x49,0xc1,0xc3,0x3,0x49,0x31,0xd3,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x32,0x49,0xc1,0xec,0x6,0x4c,0x89,0xcb,0x48,0xc1,0xc3,0x2e,0x4d,0x31,0xdc,0x4d,0x89,0xcb,0x49,0xc1,0xc3,0x17,0x48,0x31,0xd3,0x49,0x31,0xdb,0x48,0x8b,0x9c,0x24,0xb0,0x0,0x0,0x0,0x48,0x8b,0x74,0x24,0x18,0x4c,0x1,0xe6,0x48,0x1,0xfe,0x4c,0x89,0xc2,0x4c,0x31,0xea,0x4c,0x21,0xca,0x4c,0x31,0xea,0x48,0x1,0xd6,0x48,0x89,0xca,0x48,0xc1,0xc2,0x24,0x4c,0x1,0xde,0x49,0x89,0xf6,0x48,0x89,0xcf,0x48,0xc1,0xc7,0x1e,0x48,0x31,0xd7,0x48,0x89,0xca,0x48,0xc1,0xc2,0x19,0x48,0x31,0xfa,0x4c,0x89,0xd7,0x48,0x21,0xc7,0x4d,0x89,0xd3,0x49,0x31,0xc3,0x49,0x21,0xcb,0x49,0x31,0xfb,0x4c,0x3,0x9c,0x24,0x30,0x1,0x0,0x0,0x49,0x1,0xd3,0x48,0x3,0x8c,0x24,0x38,0x1,0x0,0x0,0x4c,0x3,0x94,0x24,0x48,0x1,0x0,0x0,0x48,0x3,0x84,0x24,0x58,0x1,0x0,0x0,0x48,0x8b,0xb4,0x24,0x68,0x1,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part55_bytes [Bindings] : part55.flatMap CheckedInstruction.bytes = part55Bytes := by
  rfl

def part55Layout : List (BitVec 64 × Nat) :=
  [(0x11167c, 4), (0x111680, 3), (0x111683, 3), (0x111686, 3), (0x111689, 3), (0x11168c, 3), (0x11168f, 8), (0x111697, 3), (0x11169a, 3), (0x11169d, 3), (0x1116a0, 3), (0x1116a3, 3), (0x1116a6, 3), (0x1116a9, 3), (0x1116ac, 5), (0x1116b1, 3), (0x1116b4, 4), (0x1116b8, 3), (0x1116bb, 3), (0x1116be, 4), (0x1116c2, 3), (0x1116c5, 3), (0x1116c8, 4), (0x1116cc, 4), (0x1116d0, 3), (0x1116d3, 4), (0x1116d7, 3), (0x1116da, 3), (0x1116dd, 3), (0x1116e0, 4), (0x1116e4, 3), (0x1116e7, 3), (0x1116ea, 5), (0x1116ef, 3), (0x1116f2, 3), (0x1116f5, 3), (0x1116f8, 3), (0x1116fb, 3), (0x1116fe, 3), (0x111701, 3), (0x111704, 3), (0x111707, 4), (0x11170b, 3), (0x11170e, 3), (0x111711, 4), (0x111715, 3), (0x111718, 3), (0x11171b, 4), (0x11171f, 3), (0x111722, 3), (0x111725, 3), (0x111728, 3), (0x11172b, 3), (0x11172e, 3), (0x111731, 4), (0x111735, 3), (0x111738, 3), (0x11173b, 4), (0x11173f, 3), (0x111742, 3), (0x111745, 4), (0x111749, 4), (0x11174d, 3), (0x111750, 4), (0x111754, 3), (0x111757, 3), (0x11175a, 4), (0x11175e, 3), (0x111761, 3), (0x111764, 8), (0x11176c, 5), (0x111771, 3), (0x111774, 3), (0x111777, 3), (0x11177a, 3), (0x11177d, 3), (0x111780, 3), (0x111783, 3), (0x111786, 3), (0x111789, 4), (0x11178d, 3), (0x111790, 3), (0x111793, 3), (0x111796, 4), (0x11179a, 3), (0x11179d, 3), (0x1117a0, 4), (0x1117a4, 3), (0x1117a7, 3), (0x1117aa, 3), (0x1117ad, 3), (0x1117b0, 3), (0x1117b3, 3), (0x1117b6, 3), (0x1117b9, 8), (0x1117c1, 3), (0x1117c4, 8), (0x1117cc, 8), (0x1117d4, 8), (0x1117dc, 8)]

theorem part55_layout [Bindings] : InstructionTrace.layout part55 = part55Layout := by
  rfl

theorem part55_ordered [Bindings] : InstructionTrace.ordered 0x11167c part55 = true := by
  rw [InstructionTrace.ordered_eq_layout, part55_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part55_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x1167c 360 = part55Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
