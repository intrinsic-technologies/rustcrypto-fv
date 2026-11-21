import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part17 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116725 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116728 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11672b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11672d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11672f 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116732 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116735 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116738 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11673b 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11673e 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116741 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116744 0xc3 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116746 1 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11674d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116750 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116753 0 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11675a 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11675d 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11675f 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116766 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116769 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11676c 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11676f 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116771 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116774 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116777 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116779 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11677b 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11677e 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116780 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116783 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116785 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116787 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11678a 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x11678c 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116794 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116797 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11679b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11679e 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1167a1 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1167a3 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1167a7 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1167a9 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1167ac 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167ae 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1167b1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1167b3 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167b5 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1167b8 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1167ba 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167bc 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1167bf 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167c1 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1167c4 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1167c7 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1167c9 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1167cc 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1167cf 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1167d2 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x1167d5 0x4a7484aa) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167da 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167dd 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167e0 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167e3 0xc7 0x13 rfl rfl) (by x86_local)]

def part17Bytes : List UInt8 :=
  [0x44,0x89,0xe7,0xc1,0xc7,0xa,0x31,0xd1,0x31,0xcf,0x44,0x89,0xf9,0x44,0x21,0xc9,0x45,0x89,0xfd,0x45,0x31,0xcd,0x45,0x21,0xe5,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0xc1,0xc1,0x19,0x41,0x1,0xc5,0x8b,0x84,0x24,0xac,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x8b,0xb4,0x24,0xb0,0x0,0x0,0x0,0xc1,0xee,0x3,0x44,0x89,0xc1,0xc1,0xc1,0xf,0x31,0xc6,0x44,0x89,0xc0,0xc1,0xc0,0xd,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0x19,0x89,0xef,0xc1,0xc7,0xe,0x31,0xcf,0x89,0xe9,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x84,0x24,0x88,0x0,0x0,0x0,0x44,0x1,0xc1,0x89,0x4c,0x24,0x50,0x44,0x89,0xc1,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x40,0x1,0xf2,0x48,0x89,0xde,0x89,0xf0,0xc1,0xc0,0x1a,0x1,0xca,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd1,0x44,0x31,0xf1,0x21,0xf1,0x44,0x31,0xf1,0x41,0x1,0xd3,0x41,0x1,0xcb,0x44,0x1,0xd8,0x5,0xaa,0x84,0x74,0x4a,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13]

set_option maxRecDepth 4096 in
theorem part17_bytes [Bindings] : part17.flatMap CheckedInstruction.bytes = part17Bytes  := by
  rfl

def part17Layout : List (BitVec 64 × Nat) :=
  [(0x116725, 3), (0x116728, 3), (0x11672b, 2), (0x11672d, 2), (0x11672f, 3), (0x116732, 3), (0x116735, 3), (0x116738, 3), (0x11673b, 3), (0x11673e, 3), (0x116741, 3), (0x116744, 2), (0x116746, 7), (0x11674d, 3), (0x116750, 3), (0x116753, 7), (0x11675a, 3), (0x11675d, 2), (0x11675f, 7), (0x116766, 3), (0x116769, 3), (0x11676c, 3), (0x11676f, 2), (0x116771, 3), (0x116774, 3), (0x116777, 2), (0x116779, 2), (0x11677b, 3), (0x11677e, 2), (0x116780, 3), (0x116783, 2), (0x116785, 2), (0x116787, 3), (0x11678a, 2), (0x11678c, 8), (0x116794, 3), (0x116797, 4), (0x11679b, 3), (0x11679e, 3), (0x1167a1, 2), (0x1167a3, 4), (0x1167a7, 2), (0x1167a9, 3), (0x1167ac, 2), (0x1167ae, 3), (0x1167b1, 2), (0x1167b3, 2), (0x1167b5, 3), (0x1167b8, 2), (0x1167ba, 2), (0x1167bc, 3), (0x1167bf, 2), (0x1167c1, 3), (0x1167c4, 3), (0x1167c7, 2), (0x1167c9, 3), (0x1167cc, 3), (0x1167cf, 3), (0x1167d2, 3), (0x1167d5, 5), (0x1167da, 3), (0x1167dd, 3), (0x1167e0, 3), (0x1167e3, 3)]

theorem part17_layout [Bindings] : InstructionTrace.layout part17 = part17Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part17_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16725 193 = part17Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
