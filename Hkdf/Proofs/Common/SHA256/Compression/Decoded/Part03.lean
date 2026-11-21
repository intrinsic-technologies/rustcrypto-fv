import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part03 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109882 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109887 0x41 (by simp [RexNoWPrefix]) 5 (.base 9 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10988b 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10988d 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109891 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109894 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109897 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109899 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10989c 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10989f 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1098a2 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1098a5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1098a8 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x1098ab 0xc2 0x3956c25b rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1098b1 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1098b4 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1098b8 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1098bb 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098bf 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1098c2 0xfd rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1098c4 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098c7 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1098ca 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1098cd 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1098d0 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098d3 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1098d6 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098d9 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1098dc 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1098df 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1098e1 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1098e4 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1098e6 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1098e9 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1098ec 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098f0 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1098f3 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1098f5 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1098f8 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1098fb 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109900 0x41 (by simp [RexNoWPrefix]) 5 (.base 11 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109904 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109906 5 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10990a 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10990d 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109910 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109913 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109916 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x109919 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10991c 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10991f 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109922 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109925 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109929 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10992c 0xc2 0x59f111f1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109932 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109935 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109939 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10993c 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10993f 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109943 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109946 0xfd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109948 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10994a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part03Bytes : List UInt8 :=
  [0x4c,0x8b,0x4c,0x24,0x18,0x41,0x8b,0x69,0x10,0xf,0xcd,0x89,0x6c,0x24,0x24,0x41,0x89,0xd9,0x45,0x21,0xd1,0x1,0xea,0x44,0x1,0xca,0x41,0x89,0xd9,0x41,0xf7,0xd1,0x45,0x21,0xc1,0x44,0x1,0xca,0x44,0x1,0xda,0x81,0xc2,0x5b,0xc2,0x56,0x39,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xfb,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x89,0xfd,0xc1,0xc5,0xa,0x44,0x31,0xdd,0x41,0x89,0xf3,0x41,0x21,0xcb,0x41,0x89,0xf1,0x41,0x31,0xc9,0x41,0x21,0xf9,0x45,0x31,0xd9,0x41,0x1,0xe9,0x1,0xd0,0x41,0x1,0xd1,0x89,0xc2,0xc1,0xc2,0x1a,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xd3,0x89,0xc2,0xc1,0xc2,0x7,0x44,0x31,0xda,0x4c,0x8b,0x5c,0x24,0x18,0x41,0x8b,0x6b,0x14,0xf,0xcd,0x89,0x6c,0x24,0x40,0x41,0x89,0xc3,0x41,0x21,0xdb,0x41,0x1,0xe8,0x45,0x1,0xd8,0x41,0x89,0xc3,0x41,0xf7,0xd3,0x45,0x21,0xd3,0x45,0x1,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0x1e,0x44,0x1,0xc2,0x81,0xc2,0xf1,0x11,0xf1,0x59,0x45,0x89,0xc8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0xa,0x45,0x31,0xc3,0x89,0xfd,0x21,0xf5,0x41,0x89,0xf8]

set_option maxRecDepth 4096 in
theorem part03_bytes [Bindings] : part03.flatMap CheckedInstruction.bytes = part03Bytes  := by
  rfl

def part03Layout : List (BitVec 64 × Nat) :=
  [(0x109882, 5), (0x109887, 4), (0x10988b, 2), (0x10988d, 4), (0x109891, 3), (0x109894, 3), (0x109897, 2), (0x109899, 3), (0x10989c, 3), (0x10989f, 3), (0x1098a2, 3), (0x1098a5, 3), (0x1098a8, 3), (0x1098ab, 6), (0x1098b1, 3), (0x1098b4, 4), (0x1098b8, 3), (0x1098bb, 4), (0x1098bf, 3), (0x1098c2, 2), (0x1098c4, 3), (0x1098c7, 3), (0x1098ca, 3), (0x1098cd, 3), (0x1098d0, 3), (0x1098d3, 3), (0x1098d6, 3), (0x1098d9, 3), (0x1098dc, 3), (0x1098df, 2), (0x1098e1, 3), (0x1098e4, 2), (0x1098e6, 3), (0x1098e9, 3), (0x1098ec, 4), (0x1098f0, 3), (0x1098f3, 2), (0x1098f5, 3), (0x1098f8, 3), (0x1098fb, 5), (0x109900, 4), (0x109904, 2), (0x109906, 4), (0x10990a, 3), (0x10990d, 3), (0x109910, 3), (0x109913, 3), (0x109916, 3), (0x109919, 3), (0x10991c, 3), (0x10991f, 3), (0x109922, 3), (0x109925, 4), (0x109929, 3), (0x10992c, 6), (0x109932, 3), (0x109935, 4), (0x109939, 3), (0x10993c, 3), (0x10993f, 4), (0x109943, 3), (0x109946, 2), (0x109948, 2), (0x10994a, 3)]

theorem part03_layout [Bindings] : InstructionTrace.layout part03 = part03Layout := by
  rfl

theorem part03_ordered [Bindings] : InstructionTrace.ordered 0x109882 part03 = true := by
  rw [InstructionTrace.ordered_eq_layout, part03_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part03_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9882 203 = part03Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
