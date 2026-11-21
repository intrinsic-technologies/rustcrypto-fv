import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part08 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c23 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109c26 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109c28 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c2b 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x109c2e 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109c32 0xc1 0x72be5d74 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c38 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c3a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c3d 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c3f 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c42 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c44 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c46 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c49 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c4b 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109c4e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c50 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109c53 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109c56 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109c59 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c5c 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109c5f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c61 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c64 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c66 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c69 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c6b 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c6e 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c70 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c72 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109c75 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109c77 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109c7c 7 (.base 6 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109c7f 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109c81 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c85 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109c87 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c8a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c8d 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109c90 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109c92 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109c94 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109c97 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109c9a 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109c9d 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109ca0 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109ca3 0xc1 0x80deb1fe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ca9 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109cac 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109caf 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109cb1 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109cb4 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109cb7 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109cb9 0xdf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109cbb 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109cbe 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109cc1 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109cc4 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109cc7 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109cca 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ccd 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109ccf 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109cd1 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109cd4 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part08Bytes : List UInt8 :=
  [0x44,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xc1,0x41,0x1,0xc9,0x42,0x8d,0xc,0xe,0x81,0xc1,0x74,0x5d,0xbe,0x72,0x89,0xde,0xc1,0xc6,0x1e,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x89,0xde,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xff,0x21,0xd7,0x45,0x89,0xf9,0x41,0x31,0xd1,0x41,0x21,0xd9,0x41,0x31,0xf9,0x41,0x1,0xf1,0x1,0xc8,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0x1a,0x89,0xc6,0xc1,0xc6,0x15,0x31,0xce,0x89,0xc1,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x7e,0x34,0xf,0xcf,0x89,0x7c,0x24,0x10,0x89,0xc6,0x44,0x21,0xd6,0x41,0x1,0xf8,0x41,0x1,0xf0,0x89,0xc6,0xf7,0xd6,0x44,0x21,0xde,0x41,0x1,0xf0,0x44,0x89,0xce,0xc1,0xc6,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xfe,0xb1,0xde,0x80,0x44,0x89,0xcf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xce,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xdf,0x44,0x21,0xff,0x41,0x89,0xde,0x45,0x31,0xfe,0x45,0x21,0xce,0x41,0x31,0xfe,0x41,0x1,0xf6,0x1,0xca,0x89,0xd6,0xc1,0xc6,0x1a,0x41,0x1,0xce]

set_option maxRecDepth 4096 in
theorem part08_bytes [Bindings] : part08.flatMap CheckedInstruction.bytes = part08Bytes  := by
  rfl

def part08Layout : List (BitVec 64 × Nat) :=
  [(0x109c23, 3), (0x109c26, 2), (0x109c28, 3), (0x109c2b, 3), (0x109c2e, 4), (0x109c32, 6), (0x109c38, 2), (0x109c3a, 3), (0x109c3d, 2), (0x109c3f, 3), (0x109c42, 2), (0x109c44, 2), (0x109c46, 3), (0x109c49, 2), (0x109c4b, 3), (0x109c4e, 2), (0x109c50, 3), (0x109c53, 3), (0x109c56, 3), (0x109c59, 3), (0x109c5c, 3), (0x109c5f, 2), (0x109c61, 3), (0x109c64, 2), (0x109c66, 3), (0x109c69, 2), (0x109c6b, 3), (0x109c6e, 2), (0x109c70, 2), (0x109c72, 3), (0x109c75, 2), (0x109c77, 5), (0x109c7c, 3), (0x109c7f, 2), (0x109c81, 4), (0x109c85, 2), (0x109c87, 3), (0x109c8a, 3), (0x109c8d, 3), (0x109c90, 2), (0x109c92, 2), (0x109c94, 3), (0x109c97, 3), (0x109c9a, 3), (0x109c9d, 3), (0x109ca0, 3), (0x109ca3, 6), (0x109ca9, 3), (0x109cac, 3), (0x109caf, 2), (0x109cb1, 3), (0x109cb4, 3), (0x109cb7, 2), (0x109cb9, 2), (0x109cbb, 3), (0x109cbe, 3), (0x109cc1, 3), (0x109cc4, 3), (0x109cc7, 3), (0x109cca, 3), (0x109ccd, 2), (0x109ccf, 2), (0x109cd1, 3), (0x109cd4, 3)]

theorem part08_layout [Bindings] : InstructionTrace.layout part08 = part08Layout := by
  rfl

theorem part08_ordered [Bindings] : InstructionTrace.ordered 0x109c23 part08 = true := by
  rw [InstructionTrace.ordered_eq_layout, part08_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part08_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9c23 180 = part08Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
