import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part05 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109a10 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a13 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109a16 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a1a 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109a1c 0xc2 0xab1c5ed5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a22 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a25 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109a28 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a2b 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a2e 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109a31 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a33 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109a36 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a39 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109a3c 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109a3f 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109a42 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109a45 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a48 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109a4a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a4c 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109a4f 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109a52 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a54 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109a57 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109a59 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a5b 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109a5e 0xd3 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109a60 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109a65 5 (.base 2 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109a68 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109a6a 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109a6e 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109a70 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a72 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a74 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109a76 0xfa rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109a78 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109a7a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109a7c 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x109a7e 2 (.sib 3 (some 0) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109a81 0xc2 0xd807aa98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a87 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a8a 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a8d 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a90 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109a93 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a95 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109a98 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109a9b 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109a9d 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109aa0 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109aa3 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109aa6 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109aa9 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109aac 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109aae 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109ab0 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ab3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ab5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ab8 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109abb 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109abe 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ac1 0xd3 rfl) (by x86_local)]

def part05Bytes : List UInt8 :=
  [0x44,0x1,0xd3,0x45,0x89,0xda,0x41,0xc1,0xc2,0x1e,0x1,0xda,0x81,0xc2,0xd5,0x5e,0x1c,0xab,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xd3,0x44,0x89,0xdd,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xc3,0x44,0x21,0xcb,0x45,0x89,0xc2,0x45,0x31,0xca,0x45,0x21,0xda,0x41,0x31,0xda,0x41,0x1,0xea,0x1,0xd7,0x89,0xfb,0xc1,0xc3,0x1a,0x41,0x1,0xd2,0x89,0xfa,0xc1,0xc2,0x15,0x31,0xda,0x89,0xfb,0xc1,0xc3,0x7,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x20,0xf,0xcd,0x89,0x6c,0x24,0x60,0x89,0xfa,0x21,0xf2,0x1,0xe8,0x1,0xd0,0x89,0xfa,0xf7,0xd2,0x21,0xca,0x1,0xd0,0x8d,0x14,0x3,0x81,0xc2,0x98,0xaa,0x7,0xd8,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xc3,0x44,0x89,0xd5,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xdb,0x44,0x21,0xc3,0x44,0x89,0xd8,0x44,0x31,0xc0,0x44,0x21,0xd0,0x31,0xd8,0x1,0xe8,0x41,0x1,0xd1,0x1,0xd0,0x44,0x89,0xca,0xc1,0xc2,0x1a,0x44,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xd3]

set_option maxRecDepth 4096 in
theorem part05_bytes [Bindings] : part05.flatMap CheckedInstruction.bytes = part05Bytes  := by
  rfl

def part05Layout : List (BitVec 64 × Nat) :=
  [(0x109a10, 3), (0x109a13, 3), (0x109a16, 4), (0x109a1a, 2), (0x109a1c, 6), (0x109a22, 3), (0x109a25, 3), (0x109a28, 3), (0x109a2b, 3), (0x109a2e, 3), (0x109a31, 2), (0x109a33, 3), (0x109a36, 3), (0x109a39, 3), (0x109a3c, 3), (0x109a3f, 3), (0x109a42, 3), (0x109a45, 3), (0x109a48, 2), (0x109a4a, 2), (0x109a4c, 3), (0x109a4f, 3), (0x109a52, 2), (0x109a54, 3), (0x109a57, 2), (0x109a59, 2), (0x109a5b, 3), (0x109a5e, 2), (0x109a60, 5), (0x109a65, 3), (0x109a68, 2), (0x109a6a, 4), (0x109a6e, 2), (0x109a70, 2), (0x109a72, 2), (0x109a74, 2), (0x109a76, 2), (0x109a78, 2), (0x109a7a, 2), (0x109a7c, 2), (0x109a7e, 3), (0x109a81, 6), (0x109a87, 3), (0x109a8a, 3), (0x109a8d, 3), (0x109a90, 3), (0x109a93, 2), (0x109a95, 3), (0x109a98, 3), (0x109a9b, 2), (0x109a9d, 3), (0x109aa0, 3), (0x109aa3, 3), (0x109aa6, 3), (0x109aa9, 3), (0x109aac, 2), (0x109aae, 2), (0x109ab0, 3), (0x109ab3, 2), (0x109ab5, 3), (0x109ab8, 3), (0x109abb, 3), (0x109abe, 3), (0x109ac1, 2)]

theorem part05_layout [Bindings] : InstructionTrace.layout part05 = part05Layout := by
  rfl

theorem part05_ordered [Bindings] : InstructionTrace.ordered 0x109a10 part05 = true := by
  rw [InstructionTrace.ordered_eq_layout, part05_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part05_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9a10 179 = part05Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
