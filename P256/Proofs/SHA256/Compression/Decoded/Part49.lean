import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part49 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f12 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117f15 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117f17 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f19 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f1c 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117f1f 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f22 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f25 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f28 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f2b 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117f2e 0xeb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117f30 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117f32 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f35 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f38 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f3c 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117f3f 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f42 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f45 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117f48 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117f4b 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f4f 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f52 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f55 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f59 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f5c 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117f5f 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f62 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f65 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f68 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117f6b 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f6e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f71 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f74 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117f77 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117f7a 0xc7 0x90befffa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f80 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f83 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f87 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117f8a 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f8d 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f90 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f93 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f97 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f9a 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117f9d 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f9f 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117fa2 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117fa5 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117fa8 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117fab 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117fae 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117fb0 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117fb3 0x44 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117fb6 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117fb9 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117fbc 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117fbf 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117fc2 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117fc4 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117fc7 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117fc9 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117fcb 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117fce 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part49Bytes : List UInt8 :=
  [0x45,0x31,0xd9,0x89,0xd3,0x21,0xcb,0x41,0x89,0xd3,0x41,0x31,0xcb,0x45,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x41,0x1,0xf8,0x41,0x1,0xfb,0x89,0xeb,0x89,0xef,0xc1,0xc7,0xf,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xd,0x41,0x31,0xf9,0xc1,0xeb,0xa,0x44,0x31,0xcb,0x44,0x89,0xc7,0xc1,0xc7,0x1a,0x44,0x8b,0x24,0x24,0x41,0x1,0xdc,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xf9,0x44,0x89,0xc7,0xc1,0xc7,0x7,0x44,0x31,0xcf,0x41,0x89,0xf1,0x41,0x31,0xc1,0x45,0x21,0xc1,0x41,0x31,0xc1,0x45,0x1,0xe5,0x45,0x1,0xcd,0x44,0x1,0xef,0x81,0xc7,0xfa,0xff,0xbe,0x90,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xcb,0x45,0x89,0xde,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xd3,0x21,0xd3,0x45,0x89,0xd1,0x41,0x31,0xd1,0x45,0x21,0xd9,0x41,0x31,0xd9,0x45,0x1,0xf1,0x1,0xf9,0x41,0x1,0xf9,0x44,0x89,0xfd,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xcf,0xc1,0xc7,0x1a,0x44,0x8b,0x7c,0x24,0x4]

set_option maxRecDepth 4096 in
theorem part49_bytes [Bindings] : part49.flatMap CheckedInstruction.bytes = part49Bytes  := by
  rfl

def part49Layout : List (BitVec 64 × Nat) :=
  [(0x117f12, 3), (0x117f15, 2), (0x117f17, 2), (0x117f19, 3), (0x117f1c, 3), (0x117f1f, 3), (0x117f22, 3), (0x117f25, 3), (0x117f28, 3), (0x117f2b, 3), (0x117f2e, 2), (0x117f30, 2), (0x117f32, 3), (0x117f35, 3), (0x117f38, 4), (0x117f3c, 3), (0x117f3f, 3), (0x117f42, 3), (0x117f45, 3), (0x117f48, 3), (0x117f4b, 4), (0x117f4f, 3), (0x117f52, 3), (0x117f55, 4), (0x117f59, 3), (0x117f5c, 3), (0x117f5f, 3), (0x117f62, 3), (0x117f65, 3), (0x117f68, 3), (0x117f6b, 3), (0x117f6e, 3), (0x117f71, 3), (0x117f74, 3), (0x117f77, 3), (0x117f7a, 6), (0x117f80, 3), (0x117f83, 4), (0x117f87, 3), (0x117f8a, 3), (0x117f8d, 3), (0x117f90, 3), (0x117f93, 4), (0x117f97, 3), (0x117f9a, 3), (0x117f9d, 2), (0x117f9f, 3), (0x117fa2, 3), (0x117fa5, 3), (0x117fa8, 3), (0x117fab, 3), (0x117fae, 2), (0x117fb0, 3), (0x117fb3, 3), (0x117fb6, 3), (0x117fb9, 3), (0x117fbc, 3), (0x117fbf, 3), (0x117fc2, 2), (0x117fc4, 3), (0x117fc7, 2), (0x117fc9, 2), (0x117fcb, 3), (0x117fce, 5)]

theorem part49_layout [Bindings] : InstructionTrace.layout part49 = part49Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part49_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17f12 193 = part49Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
