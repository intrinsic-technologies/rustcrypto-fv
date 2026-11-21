import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part02 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097af 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097b2 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1097b5 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1097b8 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1097bb 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1097be 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097c0 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1097c3 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1097c6 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1097ce 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097d0 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1097d3 0x47 (by simp [RexNoWPrefix]) 2 (.sib 15 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x1097d7 0x41 0xc2 0xb5c0fbcf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1097de 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1097e1 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1097e5 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1097e7 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1097ea 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1097ee 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1097f0 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1097f3 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097f6 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1097f9 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1097fc 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109801 0x45 (by simp [RexNoWPrefix]) 3 (.base 9 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109805 11) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109808 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10980d 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109810 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109813 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109816 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109819 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10981c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10981f 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109822 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109825 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109828 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10982c 0x41 (by simp [RexNoWPrefix]) 3 (.sib 9 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109830 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x109833 0x41 0xc1 0xe9b5dba5 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10983a 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10983c 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10983f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109842 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109845 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109849 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10984c 0xcd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10984e 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109850 0xcf rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109852 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109854 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109856 0xef rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109858 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10985b 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10985e 0xc3 0xe9b5dba5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109864 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109867 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10986b 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10986e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109871 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109875 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109878 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10987b 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10987f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part02Bytes : List UInt8 :=
  [0x45,0x31,0xca,0x44,0x31,0xd3,0x41,0x89,0xc1,0x49,0x89,0xf2,0x45,0x21,0xd1,0x89,0xc6,0x44,0x31,0xd6,0x4d,0x89,0xd6,0x4c,0x89,0x94,0x24,0xe8,0x0,0x0,0x0,0x21,0xce,0x44,0x31,0xce,0x47,0x8d,0x14,0x1f,0x41,0x81,0xc2,0xcf,0xfb,0xc0,0xb5,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x1,0xde,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x15,0x1,0xfe,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x45,0x31,0xcb,0x44,0x31,0xdf,0x4c,0x8b,0x4c,0x24,0x18,0x45,0x8b,0x59,0xc,0x41,0xf,0xcb,0x4c,0x89,0x5c,0x24,0x48,0x45,0x89,0xd1,0x45,0x21,0xc1,0x45,0x1,0xe3,0x45,0x1,0xd9,0x45,0x89,0xd3,0x41,0xf7,0xd3,0x41,0x21,0xd3,0x45,0x1,0xd9,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x1e,0x41,0x8d,0x1c,0x39,0x41,0x1,0xf9,0x41,0x81,0xc1,0xa5,0xdb,0xb5,0xe9,0x89,0xf7,0xc1,0xc7,0x13,0x44,0x31,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0xa,0x41,0x31,0xfb,0x89,0xcd,0x21,0xc5,0x89,0xcf,0x31,0xc7,0x21,0xf7,0x31,0xef,0x44,0x1,0xdf,0x44,0x1,0xf3,0x81,0xc3,0xa5,0xdb,0xb5,0xe9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x1a,0x44,0x1,0xcf,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x15,0x45,0x31,0xd9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x7,0x45,0x31,0xcb]

set_option maxRecDepth 4096 in
theorem part02_bytes [Bindings] : part02.flatMap CheckedInstruction.bytes = part02Bytes  := by
  rfl

def part02Layout : List (BitVec 64 × Nat) :=
  [(0x1097af, 3), (0x1097b2, 3), (0x1097b5, 3), (0x1097b8, 3), (0x1097bb, 3), (0x1097be, 2), (0x1097c0, 3), (0x1097c3, 3), (0x1097c6, 8), (0x1097ce, 2), (0x1097d0, 3), (0x1097d3, 4), (0x1097d7, 7), (0x1097de, 3), (0x1097e1, 4), (0x1097e5, 2), (0x1097e7, 3), (0x1097ea, 4), (0x1097ee, 2), (0x1097f0, 3), (0x1097f3, 3), (0x1097f6, 3), (0x1097f9, 3), (0x1097fc, 5), (0x109801, 4), (0x109805, 3), (0x109808, 5), (0x10980d, 3), (0x109810, 3), (0x109813, 3), (0x109816, 3), (0x109819, 3), (0x10981c, 3), (0x10981f, 3), (0x109822, 3), (0x109825, 3), (0x109828, 4), (0x10982c, 4), (0x109830, 3), (0x109833, 7), (0x10983a, 2), (0x10983c, 3), (0x10983f, 3), (0x109842, 3), (0x109845, 4), (0x109849, 3), (0x10984c, 2), (0x10984e, 2), (0x109850, 2), (0x109852, 2), (0x109854, 2), (0x109856, 2), (0x109858, 3), (0x10985b, 3), (0x10985e, 6), (0x109864, 3), (0x109867, 4), (0x10986b, 3), (0x10986e, 3), (0x109871, 4), (0x109875, 3), (0x109878, 3), (0x10987b, 4), (0x10987f, 3)]

theorem part02_layout [Bindings] : InstructionTrace.layout part02 = part02Layout := by
  rfl

theorem part02_ordered [Bindings] : InstructionTrace.ordered 0x1097af part02 = true := by
  rw [InstructionTrace.ordered_eq_layout, part02_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part02_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x97af 211 = part02Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
