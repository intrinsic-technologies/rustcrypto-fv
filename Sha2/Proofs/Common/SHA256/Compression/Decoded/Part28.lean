import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part28 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cac5 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cac8 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cacb 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cace 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cad0 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cad3 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cad6 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cad8 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cadb 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cadd 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cae0 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cae2 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cae5 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cae7 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10caea 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10caed 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10caef 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10caf2 0x42 (by simp [RexNoWPrefix]) 3 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10caf6 0xc3 0x2e1b2138 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cafc 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cafe 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb01 0xfa rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb03 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb05 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cb08 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb0b 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cb0e 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cb11 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cb14 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb17 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb1a 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb1d 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb20 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb23 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb26 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb29 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cb2c 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb2e 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb31 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cb33 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb35 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb38 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cb3a 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cb3c 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb3f 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10cb41 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb46 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10cb49 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb4e 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cb51 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb54 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb56 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb59 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10cb5c 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb61 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb64 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb67 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb6a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb6c 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb6f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb72 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb74 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cb77 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cb7a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part28Bytes : List UInt8 :=
  [0xc1,0xc0,0x1a,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xe2,0x31,0xf2,0x44,0x21,0xca,0x31,0xf2,0x41,0x1,0xee,0x89,0xcf,0xc1,0xc7,0x1e,0x41,0x1,0xd6,0x89,0xca,0xc1,0xc2,0x13,0x42,0x8d,0x1c,0x30,0x81,0xc3,0x38,0x21,0x1b,0x2e,0x89,0xc8,0xc1,0xc0,0xa,0x31,0xfa,0x31,0xd0,0x44,0x89,0xc2,0x44,0x21,0xea,0x45,0x89,0xc2,0x45,0x31,0xea,0x41,0x21,0xca,0x41,0x31,0xd2,0x41,0x1,0xc2,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x1,0xdb,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x41,0x1,0xda,0x89,0xef,0xc1,0xc7,0x19,0x31,0xd0,0x89,0xea,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x44,0x1,0x7c,0x24,0x48,0x44,0x1,0xff,0x48,0x89,0x7c,0x24,0x28,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x1a,0x44,0x8b,0x7c,0x24,0x38,0x41,0x1,0xd7,0x44,0x89,0xda,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xca,0x44,0x31,0xe2,0x44,0x21,0xda]

set_option maxRecDepth 4096 in
theorem part28_bytes [Bindings] : part28.flatMap CheckedInstruction.bytes = part28Bytes  := by
  rfl

def part28Layout : List (BitVec 64 × Nat) :=
  [(0x10cac5, 3), (0x10cac8, 3), (0x10cacb, 3), (0x10cace, 2), (0x10cad0, 3), (0x10cad3, 3), (0x10cad6, 2), (0x10cad8, 3), (0x10cadb, 2), (0x10cadd, 3), (0x10cae0, 2), (0x10cae2, 3), (0x10cae5, 2), (0x10cae7, 3), (0x10caea, 3), (0x10caed, 2), (0x10caef, 3), (0x10caf2, 4), (0x10caf6, 6), (0x10cafc, 2), (0x10cafe, 3), (0x10cb01, 2), (0x10cb03, 2), (0x10cb05, 3), (0x10cb08, 3), (0x10cb0b, 3), (0x10cb0e, 3), (0x10cb11, 3), (0x10cb14, 3), (0x10cb17, 3), (0x10cb1a, 3), (0x10cb1d, 3), (0x10cb20, 3), (0x10cb23, 3), (0x10cb26, 3), (0x10cb29, 3), (0x10cb2c, 2), (0x10cb2e, 3), (0x10cb31, 2), (0x10cb33, 2), (0x10cb35, 3), (0x10cb38, 2), (0x10cb3a, 2), (0x10cb3c, 3), (0x10cb3f, 2), (0x10cb41, 5), (0x10cb46, 3), (0x10cb49, 5), (0x10cb4e, 3), (0x10cb51, 3), (0x10cb54, 2), (0x10cb56, 3), (0x10cb59, 3), (0x10cb5c, 5), (0x10cb61, 3), (0x10cb64, 3), (0x10cb67, 3), (0x10cb6a, 2), (0x10cb6c, 3), (0x10cb6f, 3), (0x10cb72, 2), (0x10cb74, 3), (0x10cb77, 3), (0x10cb7a, 3)]

theorem part28_layout [Bindings] : InstructionTrace.layout part28 = part28Layout := by
  rfl

theorem part28_ordered [Bindings] : InstructionTrace.ordered 0x10cac5 part28 = true := by
  rw [InstructionTrace.ordered_eq_layout, part28_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part28_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcac5 184 = part28Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
