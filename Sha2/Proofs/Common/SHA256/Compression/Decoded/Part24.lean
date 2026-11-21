import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part24 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c7ea 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c7ed 0xc1 0xc6e00bf3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7f3 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c7f6 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c7f9 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c7fc 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c7ff 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c803 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c806 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c808 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c80b 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c80e 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c811 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c814 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c817 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c81a 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c81d 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c81f 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c822 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c825 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c827 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c82a 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c82c 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c82e 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c831 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c834 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c838 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c83b 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c83d 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c840 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c843 0 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c847 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c849 2 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c84d 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c84f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c852 0xca rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c854 0 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c858 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c85a 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c85d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c860 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c863 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c866 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c869 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c86b 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c86e 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c871 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c873 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c876 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c878 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c87b 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c87d 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c87f 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c882 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c886 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c888 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c88b 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c88e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c890 0xc7 0xd5a79147 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c896 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c899 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c89c 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c89f 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c8a1 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part24Bytes : List UInt8 :=
  [0x44,0x1,0xe9,0x81,0xc1,0xf3,0xb,0xe0,0xc6,0x44,0x89,0xe2,0xc1,0xc2,0x13,0x44,0x31,0xca,0x45,0x89,0xe2,0x41,0xc1,0xc2,0xa,0x41,0x31,0xd2,0x89,0xf2,0x44,0x21,0xf2,0x41,0x89,0xf1,0x45,0x31,0xf1,0x45,0x21,0xe1,0x41,0x31,0xd1,0x45,0x1,0xd1,0x41,0x1,0xcf,0x89,0xc2,0xc1,0xc2,0xf,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0xd,0x31,0xd1,0x89,0xea,0xc1,0xc2,0x19,0x41,0x89,0xea,0x41,0xc1,0xc2,0xe,0x41,0x31,0xd2,0x89,0xea,0xc1,0xea,0x3,0x44,0x31,0xd2,0x1,0x44,0x24,0x38,0x1,0xc2,0x89,0x54,0x24,0x58,0x89,0xc2,0xc1,0xea,0xa,0x31,0xca,0x8b,0x44,0x24,0x24,0x1,0xd0,0x4d,0x89,0xfa,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xc2,0x31,0xda,0x44,0x21,0xd2,0x31,0xda,0x1,0xc7,0x45,0x89,0xca,0x41,0xc1,0xc2,0x1e,0x1,0xd7,0x44,0x89,0xca,0xc1,0xc2,0x13,0x1,0xcf,0x81,0xc7,0x47,0x91,0xa7,0xd5,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x44,0x31,0xd2,0x31,0xd1,0x44,0x89,0xe2]

set_option maxRecDepth 4096 in
theorem part24_bytes [Bindings] : part24.flatMap CheckedInstruction.bytes = part24Bytes  := by
  rfl

def part24Layout : List (BitVec 64 × Nat) :=
  [(0x10c7ea, 3), (0x10c7ed, 6), (0x10c7f3, 3), (0x10c7f6, 3), (0x10c7f9, 3), (0x10c7fc, 3), (0x10c7ff, 4), (0x10c803, 3), (0x10c806, 2), (0x10c808, 3), (0x10c80b, 3), (0x10c80e, 3), (0x10c811, 3), (0x10c814, 3), (0x10c817, 3), (0x10c81a, 3), (0x10c81d, 2), (0x10c81f, 3), (0x10c822, 3), (0x10c825, 2), (0x10c827, 3), (0x10c82a, 2), (0x10c82c, 2), (0x10c82e, 3), (0x10c831, 3), (0x10c834, 4), (0x10c838, 3), (0x10c83b, 2), (0x10c83d, 3), (0x10c840, 3), (0x10c843, 4), (0x10c847, 2), (0x10c849, 4), (0x10c84d, 2), (0x10c84f, 3), (0x10c852, 2), (0x10c854, 4), (0x10c858, 2), (0x10c85a, 3), (0x10c85d, 3), (0x10c860, 3), (0x10c863, 3), (0x10c866, 3), (0x10c869, 2), (0x10c86b, 3), (0x10c86e, 3), (0x10c871, 2), (0x10c873, 3), (0x10c876, 2), (0x10c878, 3), (0x10c87b, 2), (0x10c87d, 2), (0x10c87f, 3), (0x10c882, 4), (0x10c886, 2), (0x10c888, 3), (0x10c88b, 3), (0x10c88e, 2), (0x10c890, 6), (0x10c896, 3), (0x10c899, 3), (0x10c89c, 3), (0x10c89f, 2), (0x10c8a1, 3)]

theorem part24_layout [Bindings] : InstructionTrace.layout part24 = part24Layout := by
  rfl

theorem part24_ordered [Bindings] : InstructionTrace.ordered 0x10c7ea part24 = true := by
  rw [InstructionTrace.ordered_eq_layout, part24_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part24_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc7ea 186 = part24Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
