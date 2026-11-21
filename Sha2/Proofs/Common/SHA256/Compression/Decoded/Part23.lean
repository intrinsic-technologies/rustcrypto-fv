import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part23 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c718 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c71b 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c71e 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c720 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c723 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c725 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c728 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c72b 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c72e 0x43 (by simp [RexNoWPrefix]) 1 (.sib 9 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c732 0xc1 0xbf597fc7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c738 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c73b 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c73f 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c742 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c746 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c749 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c74c 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c750 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c753 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c756 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c759 0x45 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c75c 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c75f 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c762 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c765 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c768 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c76b 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c76e 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c771 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c775 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c777 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c77a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c77d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c780 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c784 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c787 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c78b 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c78e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c791 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c795 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c798 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c79c 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c79f 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7a7 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c7aa 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7ae 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c7b1 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c7b5 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7b8 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c7bb 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7be 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c7c1 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7c5 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7c8 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c7cb 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7ce 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7d1 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7d4 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c7d7 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7da 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c7dd 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c7e0 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7e3 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c7e6 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part23Bytes : List UInt8 :=
  [0x44,0x31,0xd1,0x41,0x31,0xc9,0x89,0xf9,0x44,0x31,0xe9,0x21,0xd9,0x44,0x31,0xe9,0x41,0x1,0xc4,0x41,0x1,0xcc,0x43,0x8d,0xc,0x21,0x81,0xc1,0xc7,0x7f,0x59,0xbf,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x13,0x45,0x31,0xca,0x41,0x89,0xf1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd1,0x45,0x89,0xf2,0x45,0x21,0xfa,0x45,0x89,0xf4,0x45,0x31,0xfc,0x41,0x21,0xf4,0x45,0x31,0xd4,0x45,0x1,0xcc,0x41,0x1,0xc8,0x41,0x1,0xcc,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc9,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x19,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xe,0x45,0x31,0xca,0x41,0x89,0xc1,0x41,0xc1,0xe9,0x3,0x45,0x31,0xd1,0x1,0x6c,0x24,0x8,0x41,0x1,0xe9,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x41,0x89,0xe9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xc9,0x8b,0x6c,0x24,0x10,0x44,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x1a,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x44,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x41,0x89,0xd9,0x41,0x31,0xf9,0x45,0x21,0xc1,0x41,0x31,0xf9,0x41,0x1,0xed,0x45,0x1,0xcd,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x1e]

set_option maxRecDepth 4096 in
theorem part23_bytes [Bindings] : part23.flatMap CheckedInstruction.bytes = part23Bytes  := by
  rfl

def part23Layout : List (BitVec 64 × Nat) :=
  [(0x10c718, 3), (0x10c71b, 3), (0x10c71e, 2), (0x10c720, 3), (0x10c723, 2), (0x10c725, 3), (0x10c728, 3), (0x10c72b, 3), (0x10c72e, 4), (0x10c732, 6), (0x10c738, 3), (0x10c73b, 4), (0x10c73f, 3), (0x10c742, 4), (0x10c746, 3), (0x10c749, 3), (0x10c74c, 4), (0x10c750, 3), (0x10c753, 3), (0x10c756, 3), (0x10c759, 3), (0x10c75c, 3), (0x10c75f, 3), (0x10c762, 3), (0x10c765, 3), (0x10c768, 3), (0x10c76b, 3), (0x10c76e, 3), (0x10c771, 4), (0x10c775, 2), (0x10c777, 3), (0x10c77a, 3), (0x10c77d, 3), (0x10c780, 4), (0x10c784, 3), (0x10c787, 4), (0x10c78b, 3), (0x10c78e, 3), (0x10c791, 4), (0x10c795, 3), (0x10c798, 4), (0x10c79c, 3), (0x10c79f, 8), (0x10c7a7, 3), (0x10c7aa, 4), (0x10c7ae, 3), (0x10c7b1, 4), (0x10c7b5, 3), (0x10c7b8, 3), (0x10c7bb, 3), (0x10c7be, 3), (0x10c7c1, 4), (0x10c7c5, 3), (0x10c7c8, 3), (0x10c7cb, 3), (0x10c7ce, 3), (0x10c7d1, 3), (0x10c7d4, 3), (0x10c7d7, 3), (0x10c7da, 3), (0x10c7dd, 3), (0x10c7e0, 3), (0x10c7e3, 3), (0x10c7e6, 4)]

theorem part23_layout [Bindings] : InstructionTrace.layout part23 = part23Layout := by
  rfl

theorem part23_ordered [Bindings] : InstructionTrace.ordered 0x10c718 part23 = true := by
  rw [InstructionTrace.ordered_eq_layout, part23_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part23_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc718 210 = part23Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
