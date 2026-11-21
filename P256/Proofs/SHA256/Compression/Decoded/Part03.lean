import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part03 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115c52 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x115c57 0x41 (by simp [RexNoWPrefix]) 5 (.base 9 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115c5b 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115c5d 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c61 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115c64 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115c67 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c69 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c6c 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x115c6f 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115c72 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c75 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115c78 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115c7b 0xc2 0x3956c25b rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c81 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c84 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c88 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115c8b 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c8f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115c92 0xfd rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115c94 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115c97 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115c9a 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115c9d 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ca0 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115ca3 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ca6 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115ca9 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115cac 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115caf 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115cb1 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115cb4 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115cb6 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115cb9 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115cbc 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115cc0 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115cc3 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115cc5 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115cc8 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115ccb 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x115cd0 0x41 (by simp [RexNoWPrefix]) 5 (.base 11 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115cd4 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115cd6 5 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115cda 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115cdd 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ce0 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ce3 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ce6 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x115ce9 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115cec 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115cef 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115cf2 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115cf5 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115cf9 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115cfc 0xc2 0x59f111f1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d02 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d05 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d09 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d0c 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d0f 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d13 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115d16 0xfd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115d18 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d1a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part03Bytes : List UInt8 :=
  [0x4c,0x8b,0x4c,0x24,0x18,0x41,0x8b,0x69,0x10,0xf,0xcd,0x89,0x6c,0x24,0x24,0x41,0x89,0xd9,0x45,0x21,0xd1,0x1,0xea,0x44,0x1,0xca,0x41,0x89,0xd9,0x41,0xf7,0xd1,0x45,0x21,0xc1,0x44,0x1,0xca,0x44,0x1,0xda,0x81,0xc2,0x5b,0xc2,0x56,0x39,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xfb,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x89,0xfd,0xc1,0xc5,0xa,0x44,0x31,0xdd,0x41,0x89,0xf3,0x41,0x21,0xcb,0x41,0x89,0xf1,0x41,0x31,0xc9,0x41,0x21,0xf9,0x45,0x31,0xd9,0x41,0x1,0xe9,0x1,0xd0,0x41,0x1,0xd1,0x89,0xc2,0xc1,0xc2,0x1a,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xd3,0x89,0xc2,0xc1,0xc2,0x7,0x44,0x31,0xda,0x4c,0x8b,0x5c,0x24,0x18,0x41,0x8b,0x6b,0x14,0xf,0xcd,0x89,0x6c,0x24,0x40,0x41,0x89,0xc3,0x41,0x21,0xdb,0x41,0x1,0xe8,0x45,0x1,0xd8,0x41,0x89,0xc3,0x41,0xf7,0xd3,0x45,0x21,0xd3,0x45,0x1,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0x1e,0x44,0x1,0xc2,0x81,0xc2,0xf1,0x11,0xf1,0x59,0x45,0x89,0xc8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0xa,0x45,0x31,0xc3,0x89,0xfd,0x21,0xf5,0x41,0x89,0xf8]

set_option maxRecDepth 4096 in
theorem part03_bytes [Bindings] : part03.flatMap CheckedInstruction.bytes = part03Bytes  := by
  rfl

def part03Layout : List (BitVec 64 × Nat) :=
  [(0x115c52, 5), (0x115c57, 4), (0x115c5b, 2), (0x115c5d, 4), (0x115c61, 3), (0x115c64, 3), (0x115c67, 2), (0x115c69, 3), (0x115c6c, 3), (0x115c6f, 3), (0x115c72, 3), (0x115c75, 3), (0x115c78, 3), (0x115c7b, 6), (0x115c81, 3), (0x115c84, 4), (0x115c88, 3), (0x115c8b, 4), (0x115c8f, 3), (0x115c92, 2), (0x115c94, 3), (0x115c97, 3), (0x115c9a, 3), (0x115c9d, 3), (0x115ca0, 3), (0x115ca3, 3), (0x115ca6, 3), (0x115ca9, 3), (0x115cac, 3), (0x115caf, 2), (0x115cb1, 3), (0x115cb4, 2), (0x115cb6, 3), (0x115cb9, 3), (0x115cbc, 4), (0x115cc0, 3), (0x115cc3, 2), (0x115cc5, 3), (0x115cc8, 3), (0x115ccb, 5), (0x115cd0, 4), (0x115cd4, 2), (0x115cd6, 4), (0x115cda, 3), (0x115cdd, 3), (0x115ce0, 3), (0x115ce3, 3), (0x115ce6, 3), (0x115ce9, 3), (0x115cec, 3), (0x115cef, 3), (0x115cf2, 3), (0x115cf5, 4), (0x115cf9, 3), (0x115cfc, 6), (0x115d02, 3), (0x115d05, 4), (0x115d09, 3), (0x115d0c, 3), (0x115d0f, 4), (0x115d13, 3), (0x115d16, 2), (0x115d18, 2), (0x115d1a, 3)]

theorem part03_layout [Bindings] : InstructionTrace.layout part03 = part03Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part03_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15c52 203 = part03Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
