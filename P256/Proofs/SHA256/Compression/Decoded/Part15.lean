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

def part15 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11659a 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11659d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1165a2 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1165a5 0x41 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165a8 0x45 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1165ab 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165ae 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1165b1 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1165b4 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1165bc 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1165bf 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1165c2 0x41 0xc4 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1165c6 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1165c9 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1165cb 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165ce 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1165d1 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1165d3 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1165d6 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1165da 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1165dd 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165e0 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1165e3 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1165e6 0x41 0xc7 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1165ea 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165ec 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1165ef 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1165f2 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1165f5 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1165f8 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x1165fb 7 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1165ff 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116601 0 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116605 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116607 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11660a 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11660c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116611 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116614 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116616 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116619 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11661c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11661f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116622 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116625 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116627 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11662a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11662d 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11662f 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116632 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116634 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116637 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116639 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11663c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116644 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116647 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116649 0x4d 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11664c 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11664f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116652 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x116654 0x240ca1cc) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116659 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11665c 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11665f 0xca rfl) (by x86_local)]

def part15Bytes : List UInt8 :=
  [0x41,0x89,0xf7,0x4c,0x8b,0x74,0x24,0x78,0x45,0x21,0xf7,0x41,0x89,0xf5,0x45,0x31,0xf5,0x45,0x21,0xcd,0x45,0x31,0xfd,0x41,0x1,0xd5,0x4c,0x8b,0xb4,0x24,0xd8,0x0,0x0,0x0,0x41,0x1,0xc6,0xc1,0xc1,0x19,0x41,0xc1,0xc4,0xe,0x41,0x1,0xc5,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x31,0xcc,0x89,0xf9,0xc1,0xc1,0xd,0x41,0xc1,0xea,0x3,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x45,0x31,0xe2,0x45,0x89,0xc7,0x41,0xc1,0xc7,0xe,0x31,0xd1,0x41,0x31,0xc7,0x44,0x89,0xc0,0x4c,0x89,0xc6,0xc1,0xe8,0x3,0x44,0x31,0xf8,0x1,0x7c,0x24,0x34,0x1,0xf8,0x89,0x44,0x24,0x8,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x48,0x8b,0x4c,0x24,0x48,0x44,0x1,0xd1,0x1,0xc1,0x49,0x89,0xc8,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd9,0x44,0x21,0xf1,0x31,0xd9,0x48,0x89,0xdf,0x48,0x8b,0x94,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc2,0x1,0xca,0x4d,0x89,0xef,0x44,0x89,0xf9,0xc1,0xc1,0x1e,0x1,0xd0,0x5,0xcc,0xa1,0xc,0x24,0x44,0x89,0xfa,0xc1,0xc2,0x13,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part15_bytes [Bindings] : part15.flatMap CheckedInstruction.bytes = part15Bytes  := by
  rfl

def part15Layout : List (BitVec 64 × Nat) :=
  [(0x11659a, 3), (0x11659d, 5), (0x1165a2, 3), (0x1165a5, 3), (0x1165a8, 3), (0x1165ab, 3), (0x1165ae, 3), (0x1165b1, 3), (0x1165b4, 8), (0x1165bc, 3), (0x1165bf, 3), (0x1165c2, 4), (0x1165c6, 3), (0x1165c9, 2), (0x1165cb, 3), (0x1165ce, 3), (0x1165d1, 2), (0x1165d3, 3), (0x1165d6, 4), (0x1165da, 3), (0x1165dd, 3), (0x1165e0, 3), (0x1165e3, 3), (0x1165e6, 4), (0x1165ea, 2), (0x1165ec, 3), (0x1165ef, 3), (0x1165f2, 3), (0x1165f5, 3), (0x1165f8, 3), (0x1165fb, 4), (0x1165ff, 2), (0x116601, 4), (0x116605, 2), (0x116607, 3), (0x11660a, 2), (0x11660c, 5), (0x116611, 3), (0x116614, 2), (0x116616, 3), (0x116619, 3), (0x11661c, 3), (0x11661f, 3), (0x116622, 3), (0x116625, 2), (0x116627, 3), (0x11662a, 3), (0x11662d, 2), (0x11662f, 3), (0x116632, 2), (0x116634, 3), (0x116637, 2), (0x116639, 3), (0x11663c, 8), (0x116644, 3), (0x116647, 2), (0x116649, 3), (0x11664c, 3), (0x11664f, 3), (0x116652, 2), (0x116654, 5), (0x116659, 3), (0x11665c, 3), (0x11665f, 2)]

theorem part15_layout [Bindings] : InstructionTrace.layout part15 = part15Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part15_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1659a 199 = part15Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
