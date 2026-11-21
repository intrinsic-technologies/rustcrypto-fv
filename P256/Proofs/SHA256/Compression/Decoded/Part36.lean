import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part36 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117598 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11759b 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11759e 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175a1 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1175a4 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1175a7 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1175aa 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175ad 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1175b0 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1175b4 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1175b7 0x4d 0xf4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175ba 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1175bd 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1175c1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175c3 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1175c6 0x41 0xc6 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1175ca 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1175cd 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1175cf 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1175d2 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1175d5 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175d8 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1175db 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1175df 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1175e2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1175e7 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1175ea 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1175ef 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x1175f2 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1175fa 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1175fd 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117600 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117603 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117607 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11760a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11760d 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117611 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117616 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117619 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11761b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11761e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117621 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117624 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117627 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11762a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11762d 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117630 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117633 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117636 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117638 0xc1 0xc76c51a3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11763e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117641 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117644 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117647 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11764b 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11764e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117651 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117654 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117657 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11765a 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11765d 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117660 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117663 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117666 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part36Bytes : List UInt8 :=
  [0x45,0x31,0xc8,0x41,0x89,0xd9,0x45,0x21,0xd9,0x41,0x89,0xde,0x45,0x31,0xde,0x45,0x21,0xfe,0x45,0x31,0xce,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xf,0x45,0x1,0xc6,0x4d,0x89,0xf4,0x45,0x89,0xd0,0x41,0xc1,0xc0,0xd,0x1,0xca,0x41,0x89,0xee,0x41,0xc1,0xc6,0x19,0x41,0x1,0xcc,0x89,0xe9,0xc1,0xc1,0xe,0x45,0x31,0xc8,0x44,0x31,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x41,0x31,0xc9,0x48,0x8b,0x4c,0x24,0x28,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x45,0x1,0xd1,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x44,0x89,0xd1,0xc1,0xe9,0xa,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x58,0x41,0x1,0xce,0x89,0xd1,0xc1,0xc1,0x7,0x45,0x31,0xc8,0x44,0x31,0xc1,0x41,0x89,0xf0,0x41,0x31,0xc0,0x41,0x21,0xd0,0x41,0x31,0xc0,0x44,0x1,0xf7,0x44,0x1,0xc7,0x1,0xf9,0x81,0xc1,0xa3,0x51,0x6c,0xc7,0x44,0x89,0xe7,0xc1,0xc7,0x1e,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xf8,0x44,0x89,0xe7,0xc1,0xc7,0xa,0x44,0x31,0xc7,0x45,0x89,0xf8,0x41,0x21,0xd8,0x45,0x89,0xf9,0x41,0x31,0xd9,0x45,0x21,0xe1,0x45,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part36_bytes [Bindings] : part36.flatMap CheckedInstruction.bytes = part36Bytes  := by
  rfl

def part36Layout : List (BitVec 64 × Nat) :=
  [(0x117598, 3), (0x11759b, 3), (0x11759e, 3), (0x1175a1, 3), (0x1175a4, 3), (0x1175a7, 3), (0x1175aa, 3), (0x1175ad, 3), (0x1175b0, 4), (0x1175b4, 3), (0x1175b7, 3), (0x1175ba, 3), (0x1175bd, 4), (0x1175c1, 2), (0x1175c3, 3), (0x1175c6, 4), (0x1175ca, 3), (0x1175cd, 2), (0x1175cf, 3), (0x1175d2, 3), (0x1175d5, 3), (0x1175d8, 3), (0x1175db, 4), (0x1175df, 3), (0x1175e2, 5), (0x1175e7, 3), (0x1175ea, 5), (0x1175ef, 3), (0x1175f2, 8), (0x1175fa, 3), (0x1175fd, 3), (0x117600, 3), (0x117603, 4), (0x117607, 3), (0x11760a, 3), (0x11760d, 4), (0x117611, 5), (0x117616, 3), (0x117619, 2), (0x11761b, 3), (0x11761e, 3), (0x117621, 3), (0x117624, 3), (0x117627, 3), (0x11762a, 3), (0x11762d, 3), (0x117630, 3), (0x117633, 3), (0x117636, 2), (0x117638, 6), (0x11763e, 3), (0x117641, 3), (0x117644, 3), (0x117647, 4), (0x11764b, 3), (0x11764e, 3), (0x117651, 3), (0x117654, 3), (0x117657, 3), (0x11765a, 3), (0x11765d, 3), (0x117660, 3), (0x117663, 3), (0x117666, 3)]

theorem part36_layout [Bindings] : InstructionTrace.layout part36 = part36Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part36_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17598 209 = part36Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
