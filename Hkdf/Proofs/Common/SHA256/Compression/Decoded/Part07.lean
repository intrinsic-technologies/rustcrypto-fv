import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part07 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109b70 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109b72 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b75 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109b78 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109b7b 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109b7e 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109b81 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109b84 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109b87 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b8a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b8d 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b90 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b93 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b96 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b98 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b9b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b9e 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109ba0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109ba5 3 (.base 6 (.d8 44)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109ba8 3) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109baa 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bae 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109bb1 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bb4 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bb6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bb8 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109bbb 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109bbd 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bc0 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bc2 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109bc5 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bc8 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109bca 0xc1 0x550c7dc3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bd0 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109bd3 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109bd6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bd8 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109bdb 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109bde 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109be0 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109be2 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109be4 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109be6 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109be8 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109beb 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bed 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109bef 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bf2 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109bf5 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109bf8 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109bfa 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109bfd 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c00 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c02 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c05 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c08 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109c0a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109c0f 7 (.base 1 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109c12 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109c14 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c17 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109c1a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c1d 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c20 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part07Bytes : List UInt8 :=
  [0x89,0xc3,0x44,0x21,0xd3,0x41,0x89,0xc7,0x45,0x31,0xd7,0x41,0x21,0xd7,0x41,0x31,0xdf,0x41,0x1,0xf7,0x41,0x1,0xcb,0x41,0x1,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x5e,0x2c,0xf,0xcb,0x89,0x5c,0x24,0x34,0x44,0x89,0xde,0x44,0x21,0xc6,0x1,0xdf,0x1,0xf7,0x44,0x89,0xde,0xf7,0xd6,0x44,0x21,0xce,0x1,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0x1e,0x1,0xf9,0x81,0xc1,0xc3,0x7d,0xc,0x55,0x44,0x89,0xff,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xd7,0x21,0xc7,0x89,0xd3,0x31,0xc3,0x44,0x21,0xfb,0x31,0xfb,0x1,0xf3,0x41,0x1,0xca,0x44,0x89,0xd6,0xc1,0xc6,0x1a,0x1,0xcb,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x44,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x79,0x30,0xf,0xcf,0x89,0x3c,0x24,0x44,0x89,0xd1,0x44,0x21,0xd9,0x41,0x1,0xf9,0x41,0x1,0xc9]

set_option maxRecDepth 4096 in
theorem part07_bytes [Bindings] : part07.flatMap CheckedInstruction.bytes = part07Bytes  := by
  rfl

def part07Layout : List (BitVec 64 × Nat) :=
  [(0x109b70, 2), (0x109b72, 3), (0x109b75, 3), (0x109b78, 3), (0x109b7b, 3), (0x109b7e, 3), (0x109b81, 3), (0x109b84, 3), (0x109b87, 3), (0x109b8a, 3), (0x109b8d, 3), (0x109b90, 3), (0x109b93, 3), (0x109b96, 2), (0x109b98, 3), (0x109b9b, 3), (0x109b9e, 2), (0x109ba0, 5), (0x109ba5, 3), (0x109ba8, 2), (0x109baa, 4), (0x109bae, 3), (0x109bb1, 3), (0x109bb4, 2), (0x109bb6, 2), (0x109bb8, 3), (0x109bbb, 2), (0x109bbd, 3), (0x109bc0, 2), (0x109bc2, 3), (0x109bc5, 3), (0x109bc8, 2), (0x109bca, 6), (0x109bd0, 3), (0x109bd3, 3), (0x109bd6, 2), (0x109bd8, 3), (0x109bdb, 3), (0x109bde, 2), (0x109be0, 2), (0x109be2, 2), (0x109be4, 2), (0x109be6, 2), (0x109be8, 3), (0x109beb, 2), (0x109bed, 2), (0x109bef, 3), (0x109bf2, 3), (0x109bf5, 3), (0x109bf8, 2), (0x109bfa, 3), (0x109bfd, 3), (0x109c00, 2), (0x109c02, 3), (0x109c05, 3), (0x109c08, 2), (0x109c0a, 5), (0x109c0f, 3), (0x109c12, 2), (0x109c14, 3), (0x109c17, 3), (0x109c1a, 3), (0x109c1d, 3), (0x109c20, 3)]

theorem part07_layout [Bindings] : InstructionTrace.layout part07 = part07Layout := by
  rfl

theorem part07_ordered [Bindings] : InstructionTrace.ordered 0x109b70 part07 = true := by
  rw [InstructionTrace.ordered_eq_layout, part07_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part07_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9b70 179 = part07Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
