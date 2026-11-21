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

def part40 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117889 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11788b 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11788d 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117890 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117895 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117898 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11789a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11789d 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11789f 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178a1 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1178a4 0xde rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1178a6 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1178a8 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1178ad 0xde rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178af 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178b2 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178b5 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x1178b8 0x106aa070) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178bd 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178c0 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178c3 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178c6 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1178c9 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178cb 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178ce 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1178d1 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178d3 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1178d6 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178d9 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1178dc 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1178df 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1178e2 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178e5 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178e8 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1178eb 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1178ee 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178f0 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1178f3 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178f5 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1178f8 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1178fa 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1178fd 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117900 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117903 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117906 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117908 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11790b 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11790e 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117910 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117914 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x117916 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11791b 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11791d 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117920 0xf0 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x117922 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117927 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117929 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11792c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11792f 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117932 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117935 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117937 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11793a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11793d 0xf0 rfl) (by x86_local)]

def part40Bytes : List UInt8 :=
  [0x31,0xf0,0x89,0xee,0xc1,0xc6,0x15,0x44,0x8b,0x54,0x24,0x40,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0x7,0x31,0xfe,0x31,0xf0,0x44,0x89,0xfe,0x31,0xde,0x21,0xd6,0x48,0x89,0x6c,0x24,0x38,0x31,0xde,0x45,0x1,0xd3,0x41,0x1,0xf3,0x44,0x1,0xd8,0x5,0x70,0xa0,0x6a,0x10,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xe7,0x44,0x21,0xef,0x45,0x89,0xe0,0x45,0x31,0xe8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xc1,0x41,0x1,0xc0,0x89,0xc8,0xc1,0xc0,0xf,0x89,0xce,0xc1,0xc6,0xd,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xc7,0x44,0x89,0xd0,0xc1,0xe8,0x3,0x31,0xf8,0x1,0x4c,0x24,0x14,0x1,0xc8,0x48,0x89,0x44,0x24,0x40,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x48,0x8b,0x4c,0x24,0x28,0x1,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x89,0xce,0xc1,0xc6,0x15,0x31,0xc6,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xf0]

set_option maxRecDepth 4096 in
theorem part40_bytes [Bindings] : part40.flatMap CheckedInstruction.bytes = part40Bytes  := by
  rfl

def part40Layout : List (BitVec 64 × Nat) :=
  [(0x117889, 2), (0x11788b, 2), (0x11788d, 3), (0x117890, 5), (0x117895, 3), (0x117898, 2), (0x11789a, 3), (0x11789d, 2), (0x11789f, 2), (0x1178a1, 3), (0x1178a4, 2), (0x1178a6, 2), (0x1178a8, 5), (0x1178ad, 2), (0x1178af, 3), (0x1178b2, 3), (0x1178b5, 3), (0x1178b8, 5), (0x1178bd, 3), (0x1178c0, 3), (0x1178c3, 3), (0x1178c6, 3), (0x1178c9, 2), (0x1178cb, 3), (0x1178ce, 3), (0x1178d1, 2), (0x1178d3, 3), (0x1178d6, 3), (0x1178d9, 3), (0x1178dc, 3), (0x1178df, 3), (0x1178e2, 3), (0x1178e5, 3), (0x1178e8, 3), (0x1178eb, 3), (0x1178ee, 2), (0x1178f0, 3), (0x1178f3, 2), (0x1178f5, 3), (0x1178f8, 2), (0x1178fa, 3), (0x1178fd, 3), (0x117900, 3), (0x117903, 3), (0x117906, 2), (0x117908, 3), (0x11790b, 3), (0x11790e, 2), (0x117910, 4), (0x117914, 2), (0x117916, 5), (0x11791b, 2), (0x11791d, 3), (0x117920, 2), (0x117922, 5), (0x117927, 2), (0x117929, 3), (0x11792c, 3), (0x11792f, 3), (0x117932, 3), (0x117935, 2), (0x117937, 3), (0x11793a, 3), (0x11793d, 2)]

theorem part40_layout [Bindings] : InstructionTrace.layout part40 = part40Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part40_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17889 182 = part40Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
