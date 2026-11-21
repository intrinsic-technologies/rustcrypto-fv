import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part18 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1167e6 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167e8 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1167eb 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1167ee 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167f0 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1167f3 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1167f6 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1167f9 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1167fc 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1167ff 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116802 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116804 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116807 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x116809 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11680e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116811 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116814 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116817 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11681a 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11681c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11681f 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116822 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116825 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116829 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11682b 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11682d 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116830 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116833 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116836 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11683a 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11683c 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11683f 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116842 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116845 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116849 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x11684c 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116850 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x116853 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116858 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x11685b 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11685f 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116862 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116866 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116868 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11686b 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11686e 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116871 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116874 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116877 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116879 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11687c 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11687f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116881 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116883 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116886 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116889 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11688c 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11688f 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116892 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116896 0xc1 0x5cb0a9dc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11689c 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11689e 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168a1 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1168a4 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part18Bytes : List UInt8 :=
  [0x31,0xcf,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xf9,0x45,0x89,0xe0,0x45,0x21,0xf8,0x44,0x89,0xe7,0x44,0x31,0xff,0x44,0x21,0xef,0x44,0x31,0xc7,0x1,0xcf,0x41,0x1,0xc1,0x1,0xc7,0x44,0x8b,0x44,0x24,0x14,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x44,0x89,0xc1,0xc1,0xc1,0xe,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xe8,0x3,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x19,0x89,0xd3,0xc1,0xc3,0xe,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xe8,0x3,0x41,0x31,0xd8,0x1,0x6c,0x24,0x64,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x78,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x6c,0x24,0x28,0x1,0xc5,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x1,0xc5,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xf1,0x44,0x31,0xd1,0x44,0x21,0xc9,0x44,0x31,0xd1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x30,0x81,0xc1,0xdc,0xa9,0xb0,0x5c,0x89,0xf8,0xc1,0xc0,0x1e,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x13]

set_option maxRecDepth 4096 in
theorem part18_bytes [Bindings] : part18.flatMap CheckedInstruction.bytes = part18Bytes  := by
  rfl

def part18Layout : List (BitVec 64 × Nat) :=
  [(0x1167e6, 2), (0x1167e8, 3), (0x1167eb, 3), (0x1167ee, 2), (0x1167f0, 3), (0x1167f3, 3), (0x1167f6, 3), (0x1167f9, 3), (0x1167fc, 3), (0x1167ff, 3), (0x116802, 2), (0x116804, 3), (0x116807, 2), (0x116809, 5), (0x11680e, 3), (0x116811, 3), (0x116814, 3), (0x116817, 3), (0x11681a, 2), (0x11681c, 3), (0x11681f, 3), (0x116822, 3), (0x116825, 4), (0x116829, 2), (0x11682b, 2), (0x11682d, 3), (0x116830, 3), (0x116833, 3), (0x116836, 4), (0x11683a, 2), (0x11683c, 3), (0x11683f, 3), (0x116842, 3), (0x116845, 4), (0x116849, 3), (0x11684c, 4), (0x116850, 3), (0x116853, 5), (0x116858, 3), (0x11685b, 4), (0x11685f, 3), (0x116862, 4), (0x116866, 2), (0x116868, 3), (0x11686b, 3), (0x11686e, 3), (0x116871, 3), (0x116874, 3), (0x116877, 2), (0x116879, 3), (0x11687c, 3), (0x11687f, 2), (0x116881, 2), (0x116883, 3), (0x116886, 3), (0x116889, 3), (0x11688c, 3), (0x11688f, 3), (0x116892, 4), (0x116896, 6), (0x11689c, 2), (0x11689e, 3), (0x1168a1, 3), (0x1168a4, 4)]

theorem part18_layout [Bindings] : InstructionTrace.layout part18 = part18Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part18_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x167e6 194 = part18Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
