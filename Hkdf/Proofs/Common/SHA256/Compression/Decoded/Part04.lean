import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part04 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10994d 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109950 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109953 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109956 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109959 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10995b 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10995e 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109962 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109965 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109967 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10996a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10996d 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109970 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109974 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109977 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10997c 5 (.base 2 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10997f 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109981 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109985 0xca rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109987 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109989 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10998c 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10998f 0xca rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109991 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109993 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109995 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x109998 0x43 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10999c 0xc2 0x923f82a4 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099a2 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1099a5 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099a9 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1099ac 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099b0 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099b3 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1099b6 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099ba 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099bd 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1099c0 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099c2 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099c5 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1099c8 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099cb 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1099ce 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1099d1 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1099d3 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1099d6 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1099d8 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099db 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1099de 0x41 0xc2 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099e2 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1099e5 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1099e7 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1099ea 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1099ed 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1099f2 0x41 (by simp [RexNoWPrefix]) 5 (.base 10 (.d8 28)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x1099f6 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1099f8 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1099fc 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1099ff 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a02 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109a04 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a07 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x109a0a 0x41 0xd2 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109a0d 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part04Bytes : List UInt8 :=
  [0x41,0x31,0xf0,0x45,0x21,0xc8,0x41,0x31,0xe8,0x45,0x1,0xd8,0x1,0xd1,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x1a,0x41,0x1,0xd0,0x89,0xca,0xc1,0xc2,0x15,0x44,0x31,0xda,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x18,0xf,0xcd,0x89,0x6c,0x24,0x28,0x89,0xca,0x21,0xc2,0x41,0x1,0xea,0x41,0x1,0xd2,0x89,0xca,0xf7,0xd2,0x21,0xda,0x41,0x1,0xd2,0x43,0x8d,0x14,0x13,0x81,0xc2,0xa4,0x82,0x3f,0x92,0x45,0x89,0xc2,0x41,0xc1,0xc2,0x1e,0x45,0x89,0xc3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x45,0x89,0xc2,0x41,0xc1,0xc2,0xa,0x45,0x31,0xda,0x44,0x89,0xcd,0x21,0xfd,0x45,0x89,0xcb,0x41,0x31,0xfb,0x45,0x21,0xc3,0x41,0x31,0xeb,0x45,0x1,0xd3,0x1,0xd6,0x41,0x1,0xd3,0x89,0xf2,0xc1,0xc2,0x1a,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x15,0x41,0x31,0xd2,0x89,0xf2,0xc1,0xc2,0x7,0x44,0x31,0xd2,0x4c,0x8b,0x54,0x24,0x18,0x41,0x8b,0x6a,0x1c,0xf,0xcd,0x89,0x6c,0x24,0x14,0x41,0x89,0xf2,0x41,0x21,0xca,0x1,0xeb,0x44,0x1,0xd3,0x41,0x89,0xf2,0x41,0xf7,0xd2,0x41,0x21,0xc2]

set_option maxRecDepth 4096 in
theorem part04_bytes [Bindings] : part04.flatMap CheckedInstruction.bytes = part04Bytes  := by
  rfl

def part04Layout : List (BitVec 64 × Nat) :=
  [(0x10994d, 3), (0x109950, 3), (0x109953, 3), (0x109956, 3), (0x109959, 2), (0x10995b, 3), (0x10995e, 4), (0x109962, 3), (0x109965, 2), (0x109967, 3), (0x10996a, 3), (0x10996d, 3), (0x109970, 4), (0x109974, 3), (0x109977, 5), (0x10997c, 3), (0x10997f, 2), (0x109981, 4), (0x109985, 2), (0x109987, 2), (0x109989, 3), (0x10998c, 3), (0x10998f, 2), (0x109991, 2), (0x109993, 2), (0x109995, 3), (0x109998, 4), (0x10999c, 6), (0x1099a2, 3), (0x1099a5, 4), (0x1099a9, 3), (0x1099ac, 4), (0x1099b0, 3), (0x1099b3, 3), (0x1099b6, 4), (0x1099ba, 3), (0x1099bd, 3), (0x1099c0, 2), (0x1099c2, 3), (0x1099c5, 3), (0x1099c8, 3), (0x1099cb, 3), (0x1099ce, 3), (0x1099d1, 2), (0x1099d3, 3), (0x1099d6, 2), (0x1099d8, 3), (0x1099db, 3), (0x1099de, 4), (0x1099e2, 3), (0x1099e5, 2), (0x1099e7, 3), (0x1099ea, 3), (0x1099ed, 5), (0x1099f2, 4), (0x1099f6, 2), (0x1099f8, 4), (0x1099fc, 3), (0x1099ff, 3), (0x109a02, 2), (0x109a04, 3), (0x109a07, 3), (0x109a0a, 3), (0x109a0d, 3)]

theorem part04_layout [Bindings] : InstructionTrace.layout part04 = part04Layout := by
  rfl

theorem part04_ordered [Bindings] : InstructionTrace.ordered 0x10994d part04 = true := by
  rw [InstructionTrace.ordered_eq_layout, part04_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part04_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x994d 195 = part04Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
