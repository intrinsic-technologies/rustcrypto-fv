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

def part37 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117669 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11766c 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11766f 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117672 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117674 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117677 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117679 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11767c 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11767e 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117681 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117684 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117687 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11768b 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11768e 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117691 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117694 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117697 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11769b 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11769d 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1176a1 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1176a3 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176a6 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176a8 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1176ab 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176ae 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176b1 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176b4 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176b7 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176ba 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176bc 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176bf 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176c2 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1176c4 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176c6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1176c8 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176cb 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1176cd 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1176d0 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176d2 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176d5 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1176d8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x1176da 0xd192e819) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176df 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176e2 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176e5 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176e7 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1176ea 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1176ed 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176ef 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1176f2 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1176f5 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1176f8 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1176fb 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1176fe 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117701 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117704 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117706 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117709 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11770c 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11770f 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117712 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117715 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117718 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11771a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part37Bytes : List UInt8 :=
  [0x41,0x1,0xf9,0x41,0x1,0xcb,0x41,0x1,0xc9,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xe,0x41,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xc1,0x1,0x6c,0x24,0xc,0x1,0xe9,0x89,0x4c,0x24,0x58,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf9,0x45,0x89,0xea,0x41,0x1,0xca,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xdf,0xc1,0xc7,0x15,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf9,0x89,0xd7,0x31,0xf7,0x44,0x21,0xdf,0x31,0xf7,0x44,0x1,0xd0,0x1,0xf8,0x44,0x89,0xcf,0xc1,0xc7,0x1e,0x1,0xc8,0x5,0x19,0xe8,0x92,0xd1,0x44,0x89,0xc9,0xc1,0xc1,0x13,0x31,0xf9,0x44,0x89,0xcf,0xc1,0xc7,0xa,0x31,0xcf,0x44,0x89,0xe1,0x44,0x21,0xf9,0x45,0x89,0xe5,0x45,0x31,0xfd,0x45,0x21,0xcd,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x44,0x89,0xf5,0x44,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc5,0x44,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xd1]

set_option maxRecDepth 4096 in
theorem part37_bytes [Bindings] : part37.flatMap CheckedInstruction.bytes = part37Bytes  := by
  rfl

def part37Layout : List (BitVec 64 × Nat) :=
  [(0x117669, 3), (0x11766c, 3), (0x11766f, 3), (0x117672, 2), (0x117674, 3), (0x117677, 2), (0x117679, 3), (0x11767c, 2), (0x11767e, 3), (0x117681, 3), (0x117684, 3), (0x117687, 4), (0x11768b, 3), (0x11768e, 3), (0x117691, 3), (0x117694, 3), (0x117697, 4), (0x11769b, 2), (0x11769d, 4), (0x1176a1, 2), (0x1176a3, 3), (0x1176a6, 2), (0x1176a8, 3), (0x1176ab, 3), (0x1176ae, 3), (0x1176b1, 3), (0x1176b4, 3), (0x1176b7, 3), (0x1176ba, 2), (0x1176bc, 3), (0x1176bf, 3), (0x1176c2, 2), (0x1176c4, 2), (0x1176c6, 2), (0x1176c8, 3), (0x1176cb, 2), (0x1176cd, 3), (0x1176d0, 2), (0x1176d2, 3), (0x1176d5, 3), (0x1176d8, 2), (0x1176da, 5), (0x1176df, 3), (0x1176e2, 3), (0x1176e5, 2), (0x1176e7, 3), (0x1176ea, 3), (0x1176ed, 2), (0x1176ef, 3), (0x1176f2, 3), (0x1176f5, 3), (0x1176f8, 3), (0x1176fb, 3), (0x1176fe, 3), (0x117701, 3), (0x117704, 2), (0x117706, 3), (0x117709, 3), (0x11770c, 3), (0x11770f, 3), (0x117712, 3), (0x117715, 3), (0x117718, 2), (0x11771a, 3)]

theorem part37_layout [Bindings] : InstructionTrace.layout part37 = part37Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part37_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17669 180 = part37Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
