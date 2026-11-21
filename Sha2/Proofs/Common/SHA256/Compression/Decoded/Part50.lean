import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part50 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10db23 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db26 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db28 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db2b 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db2d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db2f 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db32 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db34 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db37 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10db39 0xcb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db3b 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10db3d 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10db40 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10db42 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10db44 0xc7 0xa4506ceb rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db4a 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db4d 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db50 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db53 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db56 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db58 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10db5b 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10db5f 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db62 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10db65 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db68 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10db6b 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10db6e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db71 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10db73 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10db76 0xfa rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10db78 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db7a 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db7d 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db80 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db83 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db86 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db89 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10db8b 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db8e 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db90 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db92 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db95 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db97 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db9a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db9c 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db9e 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dba1 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dba3 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dba8 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dbaa 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dbac 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dbae 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10dbb1 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dbb3 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dbb6 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dbb8 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10dbba 0xc7 0xbef9a3f7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dbc0 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dbc2 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dbc5 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dbc7 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dbca 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dbcc 0xc5 rfl) (by x86_local)]

def part50Bytes : List UInt8 :=
  [0x41,0x1,0xef,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xcf,0xc1,0xc7,0x7,0x31,0xdf,0x44,0x89,0xc3,0x31,0xf3,0x21,0xcb,0x31,0xf3,0x44,0x1,0xf8,0x1,0xd8,0x1,0xc7,0x81,0xc7,0xeb,0x6c,0x50,0xa4,0x44,0x89,0xc8,0xc1,0xc0,0x1e,0x44,0x89,0xcb,0xc1,0xc3,0x13,0x31,0xc3,0x45,0x89,0xce,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xdb,0x44,0x21,0xd3,0x44,0x89,0xd8,0x44,0x31,0xd0,0x44,0x21,0xc8,0x31,0xd8,0x44,0x1,0xf0,0x1,0xfa,0x1,0xf8,0x44,0x89,0xe5,0x44,0x89,0xe7,0xc1,0xc7,0xf,0x44,0x89,0xe3,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xd7,0xc1,0xc7,0x1a,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x40,0x1,0xeb,0x1,0xf3,0x89,0xce,0x44,0x31,0xc6,0x21,0xd6,0x44,0x31,0xc6,0x1,0xf3,0x1,0xdf,0x81,0xc7,0xf7,0xa3,0xf9,0xbe,0x89,0xc6,0xc1,0xc6,0x1e,0x89,0xc3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xc5]

set_option maxRecDepth 4096 in
theorem part50_bytes [Bindings] : part50.flatMap CheckedInstruction.bytes = part50Bytes  := by
  rfl

def part50Layout : List (BitVec 64 × Nat) :=
  [(0x10db23, 3), (0x10db26, 2), (0x10db28, 3), (0x10db2b, 2), (0x10db2d, 2), (0x10db2f, 3), (0x10db32, 2), (0x10db34, 3), (0x10db37, 2), (0x10db39, 2), (0x10db3b, 2), (0x10db3d, 3), (0x10db40, 2), (0x10db42, 2), (0x10db44, 6), (0x10db4a, 3), (0x10db4d, 3), (0x10db50, 3), (0x10db53, 3), (0x10db56, 2), (0x10db58, 3), (0x10db5b, 4), (0x10db5f, 3), (0x10db62, 3), (0x10db65, 3), (0x10db68, 3), (0x10db6b, 3), (0x10db6e, 3), (0x10db71, 2), (0x10db73, 3), (0x10db76, 2), (0x10db78, 2), (0x10db7a, 3), (0x10db7d, 3), (0x10db80, 3), (0x10db83, 3), (0x10db86, 3), (0x10db89, 2), (0x10db8b, 3), (0x10db8e, 2), (0x10db90, 2), (0x10db92, 3), (0x10db95, 2), (0x10db97, 3), (0x10db9a, 2), (0x10db9c, 2), (0x10db9e, 3), (0x10dba1, 2), (0x10dba3, 5), (0x10dba8, 2), (0x10dbaa, 2), (0x10dbac, 2), (0x10dbae, 3), (0x10dbb1, 2), (0x10dbb3, 3), (0x10dbb6, 2), (0x10dbb8, 2), (0x10dbba, 6), (0x10dbc0, 2), (0x10dbc2, 3), (0x10dbc5, 2), (0x10dbc7, 3), (0x10dbca, 2), (0x10dbcc, 2)]

theorem part50_layout [Bindings] : InstructionTrace.layout part50 = part50Layout := by
  rfl

theorem part50_ordered [Bindings] : InstructionTrace.ordered 0x10db23 part50 = true := by
  rw [InstructionTrace.ordered_eq_layout, part50_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part50_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdb23 171 = part50Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
