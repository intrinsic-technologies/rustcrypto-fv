import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part08 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ff3 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115ff6 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ff8 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ffb 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115ffe 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116002 0xc1 0x72be5d74 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116008 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11600a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11600d 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11600f 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116012 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116014 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116016 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116019 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11601b 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x11601e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116020 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116023 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116026 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116029 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11602c 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11602f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116031 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116034 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116036 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116039 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11603b 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11603e 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116040 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116042 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116045 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116047 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11604c 7 (.base 6 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x11604f 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116051 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116055 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116057 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11605a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11605d 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116060 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x116062 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116064 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116067 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11606a 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11606d 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116070 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116073 0xc1 0x80deb1fe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116079 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11607c 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11607f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116081 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116084 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116087 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116089 0xdf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11608b 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11608e 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116091 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116094 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116097 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11609a 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11609d 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11609f 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1160a1 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1160a4 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part08Bytes : List UInt8 :=
  [0x44,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xc1,0x41,0x1,0xc9,0x42,0x8d,0xc,0xe,0x81,0xc1,0x74,0x5d,0xbe,0x72,0x89,0xde,0xc1,0xc6,0x1e,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x89,0xde,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xff,0x21,0xd7,0x45,0x89,0xf9,0x41,0x31,0xd1,0x41,0x21,0xd9,0x41,0x31,0xf9,0x41,0x1,0xf1,0x1,0xc8,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0x1a,0x89,0xc6,0xc1,0xc6,0x15,0x31,0xce,0x89,0xc1,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x7e,0x34,0xf,0xcf,0x89,0x7c,0x24,0x10,0x89,0xc6,0x44,0x21,0xd6,0x41,0x1,0xf8,0x41,0x1,0xf0,0x89,0xc6,0xf7,0xd6,0x44,0x21,0xde,0x41,0x1,0xf0,0x44,0x89,0xce,0xc1,0xc6,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xfe,0xb1,0xde,0x80,0x44,0x89,0xcf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xce,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xdf,0x44,0x21,0xff,0x41,0x89,0xde,0x45,0x31,0xfe,0x45,0x21,0xce,0x41,0x31,0xfe,0x41,0x1,0xf6,0x1,0xca,0x89,0xd6,0xc1,0xc6,0x1a,0x41,0x1,0xce]

set_option maxRecDepth 4096 in
theorem part08_bytes [Bindings] : part08.flatMap CheckedInstruction.bytes = part08Bytes  := by
  rfl

def part08Layout : List (BitVec 64 × Nat) :=
  [(0x115ff3, 3), (0x115ff6, 2), (0x115ff8, 3), (0x115ffb, 3), (0x115ffe, 4), (0x116002, 6), (0x116008, 2), (0x11600a, 3), (0x11600d, 2), (0x11600f, 3), (0x116012, 2), (0x116014, 2), (0x116016, 3), (0x116019, 2), (0x11601b, 3), (0x11601e, 2), (0x116020, 3), (0x116023, 3), (0x116026, 3), (0x116029, 3), (0x11602c, 3), (0x11602f, 2), (0x116031, 3), (0x116034, 2), (0x116036, 3), (0x116039, 2), (0x11603b, 3), (0x11603e, 2), (0x116040, 2), (0x116042, 3), (0x116045, 2), (0x116047, 5), (0x11604c, 3), (0x11604f, 2), (0x116051, 4), (0x116055, 2), (0x116057, 3), (0x11605a, 3), (0x11605d, 3), (0x116060, 2), (0x116062, 2), (0x116064, 3), (0x116067, 3), (0x11606a, 3), (0x11606d, 3), (0x116070, 3), (0x116073, 6), (0x116079, 3), (0x11607c, 3), (0x11607f, 2), (0x116081, 3), (0x116084, 3), (0x116087, 2), (0x116089, 2), (0x11608b, 3), (0x11608e, 3), (0x116091, 3), (0x116094, 3), (0x116097, 3), (0x11609a, 3), (0x11609d, 2), (0x11609f, 2), (0x1160a1, 3), (0x1160a4, 3)]

theorem part08_layout [Bindings] : InstructionTrace.layout part08 = part08Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part08_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15ff3 180 = part08Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
