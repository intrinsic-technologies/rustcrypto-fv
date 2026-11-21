import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part32 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ae81 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae85 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae88 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10ae8b 0x41 0xeb 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae8f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10ae92 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae96 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10ae99 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae9e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10aea1 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aea5 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aea8 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aeab 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10aeae 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aeb2 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aeb5 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10aeb8 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aebc 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aebf 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aec2 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aec5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aec8 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aecb 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10aece 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aed1 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aed4 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aed7 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10aeda 0x46 (by simp [RexNoWPrefix]) 3 (.sib 2 (some 13) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10aede 0x41 0xc3 0x81c2c92e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aee5 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aee7 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aeea 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10aeed 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aef1 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aef4 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10aef7 0x41 0xc7 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aefb 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aefe 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10af01 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10af04 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10af06 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10af08 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af0a 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af0d 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10af10 0xc3 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af13 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af16 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af19 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af1d 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af20 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af23 0x41 0xc7 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af27 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af2a 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af2d 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af31 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af34 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10af37 0xeb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10af39 0xeb 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af3c 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10af3f 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af44 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af47 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10af4a 3 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af4e 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part32Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0xe,0x45,0x31,0xd9,0x45,0x89,0xe3,0x41,0xc1,0xeb,0x3,0x45,0x31,0xcb,0x1,0x5c,0x24,0x58,0x41,0x1,0xdb,0x44,0x89,0x5c,0x24,0x78,0x41,0x89,0xd9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x14,0x44,0x1,0xcd,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x7,0x44,0x31,0xca,0x41,0x89,0xc9,0x45,0x31,0xc1,0x45,0x21,0xd1,0x45,0x31,0xc1,0x41,0x1,0xed,0x45,0x1,0xcd,0x46,0x8d,0x1c,0x2a,0x41,0x81,0xc3,0x2e,0xc9,0xc2,0x81,0x89,0xf2,0xc1,0xc2,0x1e,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x13,0x41,0x31,0xd1,0x41,0x89,0xf7,0x41,0xc1,0xc7,0xa,0x45,0x31,0xcf,0x41,0x89,0xc1,0x41,0x21,0xf9,0x89,0xc2,0x31,0xfa,0x21,0xf2,0x44,0x31,0xca,0x44,0x89,0xe3,0xc1,0xc3,0xf,0x44,0x1,0xfa,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xd,0x45,0x1,0xde,0x41,0x89,0xef,0x41,0xc1,0xc7,0x19,0x44,0x1,0xda,0x41,0x89,0xeb,0x41,0xc1,0xc3,0xe,0x41,0x31,0xd9,0x45,0x31,0xfb,0x89,0xeb,0xc1,0xeb,0x3,0x44,0x31,0xdb,0x44,0x8b,0x6c,0x24,0x10,0x45,0x1,0xe5,0x44,0x1,0xe3,0x89,0x5c,0x24,0x14,0x45,0x89,0xe3]

set_option maxRecDepth 4096 in
theorem part32_bytes [Bindings] : part32.flatMap CheckedInstruction.bytes = part32Bytes  := by
  rfl

def part32Layout : List (BitVec 64 × Nat) :=
  [(0x10ae81, 4), (0x10ae85, 3), (0x10ae88, 3), (0x10ae8b, 4), (0x10ae8f, 3), (0x10ae92, 4), (0x10ae96, 3), (0x10ae99, 5), (0x10ae9e, 3), (0x10aea1, 4), (0x10aea5, 3), (0x10aea8, 3), (0x10aeab, 3), (0x10aeae, 4), (0x10aeb2, 3), (0x10aeb5, 3), (0x10aeb8, 4), (0x10aebc, 3), (0x10aebf, 3), (0x10aec2, 3), (0x10aec5, 3), (0x10aec8, 3), (0x10aecb, 3), (0x10aece, 3), (0x10aed1, 3), (0x10aed4, 3), (0x10aed7, 3), (0x10aeda, 4), (0x10aede, 7), (0x10aee5, 2), (0x10aee7, 3), (0x10aeea, 3), (0x10aeed, 4), (0x10aef1, 3), (0x10aef4, 3), (0x10aef7, 4), (0x10aefb, 3), (0x10aefe, 3), (0x10af01, 3), (0x10af04, 2), (0x10af06, 2), (0x10af08, 2), (0x10af0a, 3), (0x10af0d, 3), (0x10af10, 3), (0x10af13, 3), (0x10af16, 3), (0x10af19, 4), (0x10af1d, 3), (0x10af20, 3), (0x10af23, 4), (0x10af27, 3), (0x10af2a, 3), (0x10af2d, 4), (0x10af31, 3), (0x10af34, 3), (0x10af37, 2), (0x10af39, 3), (0x10af3c, 3), (0x10af3f, 5), (0x10af44, 3), (0x10af47, 3), (0x10af4a, 4), (0x10af4e, 3)]

theorem part32_layout [Bindings] : InstructionTrace.layout part32 = part32Layout := by
  rfl

theorem part32_ordered [Bindings] : InstructionTrace.ordered 0x10ae81 part32 = true := by
  rw [InstructionTrace.ordered_eq_layout, part32_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part32_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xae81 208 = part32Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
