import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part47 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d8d9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d8db 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d8de 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8e0 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d8e3 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8e6 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d8e9 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d8ec 0xd7 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d8ee 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d8f3 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d8f6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8fb 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d8fe 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d901 0xfa rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d903 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d90b 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d90e 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d911 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d914 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d917 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d91a 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d91c 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d91f 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d922 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d924 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d927 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d92a 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d92d 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d930 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d933 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d936 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d938 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d93b 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10d93e 0x41 0xc3 0x78a5636f (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d945 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d947 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d94a 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d94c 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d94e 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d951 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d953 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d956 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d958 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d95b 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d95d 0xca rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d95f 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d961 0xfa rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d963 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d966 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d968 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d96b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d96e 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d971 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d975 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d978 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d97d 0xef rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d97f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d984 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d986 0xef 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d989 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d98c 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d98f 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d993 5 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d997 0xfd rfl) (by x86_local)]

def part47Bytes : List UInt8 :=
  [0x1,0xd9,0x41,0x1,0xd5,0x1,0xd1,0x44,0x89,0xf2,0xc1,0xc2,0xf,0x44,0x89,0xf7,0xc1,0xc7,0xd,0x31,0xd7,0x48,0x8b,0x54,0x24,0x40,0x44,0x1,0xf2,0x48,0x89,0x54,0x24,0x40,0x44,0x89,0xf2,0xc1,0xea,0xa,0x31,0xfa,0x44,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x41,0x1,0xd6,0x44,0x89,0xea,0xc1,0xc2,0x1a,0x44,0x89,0xef,0xc1,0xc7,0x15,0x31,0xd7,0x44,0x89,0xea,0xc1,0xc2,0x7,0x31,0xfa,0x44,0x89,0xcf,0x44,0x31,0xd7,0x44,0x21,0xef,0x44,0x31,0xd7,0x45,0x1,0xf3,0x41,0x1,0xfb,0x89,0xcf,0xc1,0xc7,0x1e,0x41,0x1,0xd3,0x41,0x81,0xc3,0x6f,0x63,0xa5,0x78,0x89,0xca,0xc1,0xc2,0x13,0x31,0xfa,0x89,0xcf,0xc1,0xc7,0xa,0x31,0xd7,0x44,0x89,0xc3,0x21,0xf3,0x44,0x89,0xc2,0x31,0xf2,0x21,0xca,0x31,0xda,0x1,0xfa,0x44,0x1,0xd8,0x89,0xef,0xc1,0xc7,0xf,0x44,0x1,0xda,0x41,0x89,0xeb,0x41,0xc1,0xc3,0xd,0x41,0x31,0xfb,0x48,0x8b,0x7c,0x24,0x28,0x1,0xef,0x48,0x89,0x7c,0x24,0x28,0x89,0xef,0xc1,0xef,0xa,0x44,0x31,0xdf,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x1a,0x8b,0x6c,0x24,0x58,0x1,0xfd]

set_option maxRecDepth 4096 in
theorem part47_bytes [Bindings] : part47.flatMap CheckedInstruction.bytes = part47Bytes  := by
  rfl

def part47Layout : List (BitVec 64 × Nat) :=
  [(0x10d8d9, 2), (0x10d8db, 3), (0x10d8de, 2), (0x10d8e0, 3), (0x10d8e3, 3), (0x10d8e6, 3), (0x10d8e9, 3), (0x10d8ec, 2), (0x10d8ee, 5), (0x10d8f3, 3), (0x10d8f6, 5), (0x10d8fb, 3), (0x10d8fe, 3), (0x10d901, 2), (0x10d903, 8), (0x10d90b, 3), (0x10d90e, 3), (0x10d911, 3), (0x10d914, 3), (0x10d917, 3), (0x10d91a, 2), (0x10d91c, 3), (0x10d91f, 3), (0x10d922, 2), (0x10d924, 3), (0x10d927, 3), (0x10d92a, 3), (0x10d92d, 3), (0x10d930, 3), (0x10d933, 3), (0x10d936, 2), (0x10d938, 3), (0x10d93b, 3), (0x10d93e, 7), (0x10d945, 2), (0x10d947, 3), (0x10d94a, 2), (0x10d94c, 2), (0x10d94e, 3), (0x10d951, 2), (0x10d953, 3), (0x10d956, 2), (0x10d958, 3), (0x10d95b, 2), (0x10d95d, 2), (0x10d95f, 2), (0x10d961, 2), (0x10d963, 3), (0x10d966, 2), (0x10d968, 3), (0x10d96b, 3), (0x10d96e, 3), (0x10d971, 4), (0x10d975, 3), (0x10d978, 5), (0x10d97d, 2), (0x10d97f, 5), (0x10d984, 2), (0x10d986, 3), (0x10d989, 3), (0x10d98c, 3), (0x10d98f, 4), (0x10d993, 4), (0x10d997, 2)]

theorem part47_layout [Bindings] : InstructionTrace.layout part47 = part47Layout := by
  rfl

theorem part47_ordered [Bindings] : InstructionTrace.ordered 0x10d8d9 part47 = true := by
  rw [InstructionTrace.ordered_eq_layout, part47_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part47_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd8d9 192 = part47Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
