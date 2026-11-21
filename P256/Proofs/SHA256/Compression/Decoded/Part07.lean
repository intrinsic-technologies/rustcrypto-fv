import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part07 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115f40 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115f42 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f45 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115f48 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115f4b 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115f4e 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115f51 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115f54 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115f57 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f5a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f5d 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f60 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f63 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115f66 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f68 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f6b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115f6e 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115f70 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115f75 3 (.base 6 (.d8 44)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115f78 3) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115f7a 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f7e 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115f81 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f84 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f86 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f88 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115f8b 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115f8d 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f90 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f92 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f95 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f98 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115f9a 0xc1 0x550c7dc3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fa0 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115fa3 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fa6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fa8 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115fab 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fae 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115fb0 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115fb2 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115fb4 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fb6 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115fb8 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fbb 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115fbd 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115fbf 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fc2 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115fc5 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115fc8 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fca 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115fcd 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fd0 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fd2 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115fd5 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115fd8 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115fda 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115fdf 7 (.base 1 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115fe2 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115fe4 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115fe7 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115fea 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115fed 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ff0 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part07Bytes : List UInt8 :=
  [0x89,0xc3,0x44,0x21,0xd3,0x41,0x89,0xc7,0x45,0x31,0xd7,0x41,0x21,0xd7,0x41,0x31,0xdf,0x41,0x1,0xf7,0x41,0x1,0xcb,0x41,0x1,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x5e,0x2c,0xf,0xcb,0x89,0x5c,0x24,0x34,0x44,0x89,0xde,0x44,0x21,0xc6,0x1,0xdf,0x1,0xf7,0x44,0x89,0xde,0xf7,0xd6,0x44,0x21,0xce,0x1,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0x1e,0x1,0xf9,0x81,0xc1,0xc3,0x7d,0xc,0x55,0x44,0x89,0xff,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xd7,0x21,0xc7,0x89,0xd3,0x31,0xc3,0x44,0x21,0xfb,0x31,0xfb,0x1,0xf3,0x41,0x1,0xca,0x44,0x89,0xd6,0xc1,0xc6,0x1a,0x1,0xcb,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x44,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x79,0x30,0xf,0xcf,0x89,0x3c,0x24,0x44,0x89,0xd1,0x44,0x21,0xd9,0x41,0x1,0xf9,0x41,0x1,0xc9]

set_option maxRecDepth 4096 in
theorem part07_bytes [Bindings] : part07.flatMap CheckedInstruction.bytes = part07Bytes  := by
  rfl

def part07Layout : List (BitVec 64 × Nat) :=
  [(0x115f40, 2), (0x115f42, 3), (0x115f45, 3), (0x115f48, 3), (0x115f4b, 3), (0x115f4e, 3), (0x115f51, 3), (0x115f54, 3), (0x115f57, 3), (0x115f5a, 3), (0x115f5d, 3), (0x115f60, 3), (0x115f63, 3), (0x115f66, 2), (0x115f68, 3), (0x115f6b, 3), (0x115f6e, 2), (0x115f70, 5), (0x115f75, 3), (0x115f78, 2), (0x115f7a, 4), (0x115f7e, 3), (0x115f81, 3), (0x115f84, 2), (0x115f86, 2), (0x115f88, 3), (0x115f8b, 2), (0x115f8d, 3), (0x115f90, 2), (0x115f92, 3), (0x115f95, 3), (0x115f98, 2), (0x115f9a, 6), (0x115fa0, 3), (0x115fa3, 3), (0x115fa6, 2), (0x115fa8, 3), (0x115fab, 3), (0x115fae, 2), (0x115fb0, 2), (0x115fb2, 2), (0x115fb4, 2), (0x115fb6, 2), (0x115fb8, 3), (0x115fbb, 2), (0x115fbd, 2), (0x115fbf, 3), (0x115fc2, 3), (0x115fc5, 3), (0x115fc8, 2), (0x115fca, 3), (0x115fcd, 3), (0x115fd0, 2), (0x115fd2, 3), (0x115fd5, 3), (0x115fd8, 2), (0x115fda, 5), (0x115fdf, 3), (0x115fe2, 2), (0x115fe4, 3), (0x115fe7, 3), (0x115fea, 3), (0x115fed, 3), (0x115ff0, 3)]

theorem part07_layout [Bindings] : InstructionTrace.layout part07 = part07Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part07_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15f40 179 = part07Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
