import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part38 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11771d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117720 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117723 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117726 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117728 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11772b 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11772e 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x117730 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117735 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x117738 1 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11773c 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11773f 0xc5 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117741 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117745 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117747 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117749 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11774c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11774e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117751 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117753 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117755 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117758 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11775a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11775d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x11775f 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117761 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117763 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117765 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117767 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11776a 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11776d 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11776f 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117772 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x117775 0x44 (by simp [RexNoWPrefix]) 0 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x117779 0x41 0xc0 0xd6990624 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117780 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117783 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117786 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117788 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11778a 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11778d 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x117790 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117795 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117797 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11779a 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11779d 0x45 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1177a0 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1177a3 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177a6 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177a9 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177ac 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1177af 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177b2 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177b5 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1177b8 0x45 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177bb 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1177be 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177c0 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177c3 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1177c5 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177c7 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177ca 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1177cc 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1177ce 0xef 0x3 rfl rfl) (by x86_local)]

def part38Bytes : List UInt8 :=
  [0xc1,0xc1,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xcf,0x44,0x89,0xd1,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x74,0x24,0x8,0x44,0x1,0xf1,0x89,0x4c,0x24,0x10,0xc1,0xed,0xa,0x31,0xc5,0x8b,0x7c,0x24,0x24,0x1,0xef,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd1,0x21,0xd9,0x31,0xd1,0x1,0xfe,0x89,0xfd,0x44,0x89,0xef,0xc1,0xc7,0x1e,0x1,0xce,0x44,0x89,0xe9,0xc1,0xc1,0x13,0x44,0x8d,0x4,0x30,0x41,0x81,0xc0,0x24,0x6,0x99,0xd6,0x44,0x89,0xe8,0xc1,0xc0,0xa,0x31,0xf9,0x31,0xc8,0x44,0x89,0xce,0x4c,0x89,0xe1,0x4c,0x89,0x64,0x24,0x38,0x21,0xce,0x45,0x89,0xcc,0x41,0x31,0xcc,0x45,0x21,0xec,0x41,0x31,0xf4,0x41,0x1,0xc4,0x44,0x89,0xd1,0x44,0x89,0xd0,0xc1,0xc0,0xf,0x45,0x1,0xc7,0x44,0x89,0xd6,0xc1,0xc6,0xd,0x45,0x1,0xc4,0x41,0x89,0xea,0x89,0xef,0xc1,0xc7,0x19,0x31,0xc6,0x89,0xe8,0xc1,0xc0,0xe,0x31,0xf8,0x89,0xef,0xc1,0xef,0x3]

set_option maxRecDepth 4096 in
theorem part38_bytes [Bindings] : part38.flatMap CheckedInstruction.bytes = part38Bytes  := by
  rfl

def part38Layout : List (BitVec 64 × Nat) :=
  [(0x11771d, 3), (0x117720, 3), (0x117723, 3), (0x117726, 2), (0x117728, 3), (0x11772b, 3), (0x11772e, 2), (0x117730, 5), (0x117735, 3), (0x117738, 4), (0x11773c, 3), (0x11773f, 2), (0x117741, 4), (0x117745, 2), (0x117747, 2), (0x117749, 3), (0x11774c, 2), (0x11774e, 3), (0x117751, 2), (0x117753, 2), (0x117755, 3), (0x117758, 2), (0x11775a, 3), (0x11775d, 2), (0x11775f, 2), (0x117761, 2), (0x117763, 2), (0x117765, 2), (0x117767, 3), (0x11776a, 3), (0x11776d, 2), (0x11776f, 3), (0x117772, 3), (0x117775, 4), (0x117779, 7), (0x117780, 3), (0x117783, 3), (0x117786, 2), (0x117788, 2), (0x11778a, 3), (0x11778d, 3), (0x117790, 5), (0x117795, 2), (0x117797, 3), (0x11779a, 3), (0x11779d, 3), (0x1177a0, 3), (0x1177a3, 3), (0x1177a6, 3), (0x1177a9, 3), (0x1177ac, 3), (0x1177af, 3), (0x1177b2, 3), (0x1177b5, 3), (0x1177b8, 3), (0x1177bb, 3), (0x1177be, 2), (0x1177c0, 3), (0x1177c3, 2), (0x1177c5, 2), (0x1177c7, 3), (0x1177ca, 2), (0x1177cc, 2), (0x1177ce, 3)]

theorem part38_layout [Bindings] : InstructionTrace.layout part38 = part38Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part38_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1771d 180 = part38Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
