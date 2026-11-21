import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part01 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115aab 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115aad 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115aaf 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ab1 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ab4 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ab7 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115aba 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115abc 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115abe 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ac6 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115ac9 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x115acb 6 (.sib 1 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115ace 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115ad0 0xc7 0x71374491 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115ad6 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115ad8 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115adb 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115ade 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115ae2 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ae5 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115ae8 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115aec 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115aef 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115af2 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115af5 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115af7 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115afa 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115b02 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115b04 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115b07 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115b0a 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115b0c 0x45 (by simp [RexNoWPrefix]) 0 (.sib 14 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x115b10 0x41 0xc0 0x71374491 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b17 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115b1a 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b1d 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115b20 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115b23 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b25 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115b28 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115b2b 0xfe rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115b2d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x115b32 0x44 (by simp [RexNoWPrefix]) 1 (.base 7 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115b36 9) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115b39 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b3e 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115b41 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115b43 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115b46 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b49 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x115b4c 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115b4f 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115b57 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115b5a 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b5d 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115b60 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115b64 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115b67 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115b6b 0x44 (by simp [RexNoWPrefix]) 3 (.sib 7 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115b6f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115b71 0xc7 0xb5c0fbcf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115b77 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115b7a 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115b7c 0xc3 0xa rfl rfl) (by x86_local)]

def part01Bytes : List UInt8 :=
  [0x31,0xce,0x31,0xf7,0x89,0xd1,0x44,0x21,0xe1,0x44,0x1,0xc9,0x44,0x1,0xe9,0x89,0xd6,0xf7,0xd6,0x4c,0x89,0x94,0x24,0x0,0x1,0x0,0x0,0x44,0x21,0xd6,0x1,0xf1,0x8d,0x34,0x39,0x1,0xcf,0x81,0xc7,0x91,0x44,0x37,0x71,0x89,0xc1,0xc1,0xc1,0x1e,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x41,0x89,0xc1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd8,0x45,0x21,0xf8,0x89,0xd9,0x44,0x31,0xf9,0x4c,0x89,0xbc,0x24,0xf8,0x0,0x0,0x0,0x21,0xc1,0x44,0x31,0xc1,0x44,0x1,0xc9,0x1,0xf9,0x45,0x8d,0x4,0x36,0x41,0x81,0xc0,0x91,0x44,0x37,0x71,0x44,0x89,0xc6,0xc1,0xc6,0x1a,0x44,0x89,0xc7,0xc1,0xc7,0x15,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0x7,0x31,0xfe,0x48,0x8b,0x7c,0x24,0x18,0x44,0x8b,0x4f,0x8,0x41,0xf,0xc9,0x4c,0x89,0x4c,0x24,0x68,0x44,0x89,0xc7,0x21,0xd7,0x45,0x1,0xd1,0x44,0x1,0xcf,0x45,0x89,0xc1,0x41,0xf7,0xd1,0x4c,0x89,0xa4,0x24,0xf0,0x0,0x0,0x0,0x45,0x21,0xe1,0x44,0x1,0xcf,0x41,0x89,0xc9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xca,0x41,0xc1,0xc2,0x13,0x44,0x8d,0x1c,0x37,0x1,0xf7,0x81,0xc7,0xcf,0xfb,0xc0,0xb5,0x48,0x89,0xde,0x89,0xcb,0xc1,0xc3,0xa]

set_option maxRecDepth 4096 in
theorem part01_bytes [Bindings] : part01.flatMap CheckedInstruction.bytes = part01Bytes  := by
  rfl

def part01Layout : List (BitVec 64 × Nat) :=
  [(0x115aab, 2), (0x115aad, 2), (0x115aaf, 2), (0x115ab1, 3), (0x115ab4, 3), (0x115ab7, 3), (0x115aba, 2), (0x115abc, 2), (0x115abe, 8), (0x115ac6, 3), (0x115ac9, 2), (0x115acb, 3), (0x115ace, 2), (0x115ad0, 6), (0x115ad6, 2), (0x115ad8, 3), (0x115adb, 3), (0x115ade, 4), (0x115ae2, 3), (0x115ae5, 3), (0x115ae8, 4), (0x115aec, 3), (0x115aef, 3), (0x115af2, 3), (0x115af5, 2), (0x115af7, 3), (0x115afa, 8), (0x115b02, 2), (0x115b04, 3), (0x115b07, 3), (0x115b0a, 2), (0x115b0c, 4), (0x115b10, 7), (0x115b17, 3), (0x115b1a, 3), (0x115b1d, 3), (0x115b20, 3), (0x115b23, 2), (0x115b25, 3), (0x115b28, 3), (0x115b2b, 2), (0x115b2d, 5), (0x115b32, 4), (0x115b36, 3), (0x115b39, 5), (0x115b3e, 3), (0x115b41, 2), (0x115b43, 3), (0x115b46, 3), (0x115b49, 3), (0x115b4c, 3), (0x115b4f, 8), (0x115b57, 3), (0x115b5a, 3), (0x115b5d, 3), (0x115b60, 4), (0x115b64, 3), (0x115b67, 4), (0x115b6b, 4), (0x115b6f, 2), (0x115b71, 6), (0x115b77, 3), (0x115b7a, 2), (0x115b7c, 3)]

theorem part01_layout [Bindings] : InstructionTrace.layout part01 = part01Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part01_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15aab 212 = part01Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
