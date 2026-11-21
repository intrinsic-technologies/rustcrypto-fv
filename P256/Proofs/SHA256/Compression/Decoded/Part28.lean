import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part28 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f75 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f78 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f7b 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f7e 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f80 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f83 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f86 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116f88 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f8b 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116f8d 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116f90 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116f92 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116f95 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f97 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116f9a 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116f9d 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116f9f 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116fa2 0x42 (by simp [RexNoWPrefix]) 3 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116fa6 0xc3 0x2e1b2138 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116fac 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116fae 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116fb1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116fb3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116fb5 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116fb8 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116fbb 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116fbe 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116fc1 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116fc4 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116fc7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116fca 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116fcd 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116fd0 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116fd3 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116fd6 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116fd9 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116fdc 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116fde 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116fe1 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116fe3 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116fe5 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116fe8 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116fea 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116fec 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116fef 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x116ff1 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116ff6 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x116ff9 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ffe 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117001 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117004 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117006 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117009 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x11700c 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117011 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117014 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117017 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11701a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11701c 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11701f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117022 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117024 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117027 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11702a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part28Bytes : List UInt8 :=
  [0xc1,0xc0,0x1a,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xe2,0x31,0xf2,0x44,0x21,0xca,0x31,0xf2,0x41,0x1,0xee,0x89,0xcf,0xc1,0xc7,0x1e,0x41,0x1,0xd6,0x89,0xca,0xc1,0xc2,0x13,0x42,0x8d,0x1c,0x30,0x81,0xc3,0x38,0x21,0x1b,0x2e,0x89,0xc8,0xc1,0xc0,0xa,0x31,0xfa,0x31,0xd0,0x44,0x89,0xc2,0x44,0x21,0xea,0x45,0x89,0xc2,0x45,0x31,0xea,0x41,0x21,0xca,0x41,0x31,0xd2,0x41,0x1,0xc2,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x1,0xdb,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x41,0x1,0xda,0x89,0xef,0xc1,0xc7,0x19,0x31,0xd0,0x89,0xea,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x44,0x1,0x7c,0x24,0x48,0x44,0x1,0xff,0x48,0x89,0x7c,0x24,0x28,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x1a,0x44,0x8b,0x7c,0x24,0x38,0x41,0x1,0xd7,0x44,0x89,0xda,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xca,0x44,0x31,0xe2,0x44,0x21,0xda]

set_option maxRecDepth 4096 in
theorem part28_bytes [Bindings] : part28.flatMap CheckedInstruction.bytes = part28Bytes  := by
  rfl

def part28Layout : List (BitVec 64 × Nat) :=
  [(0x116f75, 3), (0x116f78, 3), (0x116f7b, 3), (0x116f7e, 2), (0x116f80, 3), (0x116f83, 3), (0x116f86, 2), (0x116f88, 3), (0x116f8b, 2), (0x116f8d, 3), (0x116f90, 2), (0x116f92, 3), (0x116f95, 2), (0x116f97, 3), (0x116f9a, 3), (0x116f9d, 2), (0x116f9f, 3), (0x116fa2, 4), (0x116fa6, 6), (0x116fac, 2), (0x116fae, 3), (0x116fb1, 2), (0x116fb3, 2), (0x116fb5, 3), (0x116fb8, 3), (0x116fbb, 3), (0x116fbe, 3), (0x116fc1, 3), (0x116fc4, 3), (0x116fc7, 3), (0x116fca, 3), (0x116fcd, 3), (0x116fd0, 3), (0x116fd3, 3), (0x116fd6, 3), (0x116fd9, 3), (0x116fdc, 2), (0x116fde, 3), (0x116fe1, 2), (0x116fe3, 2), (0x116fe5, 3), (0x116fe8, 2), (0x116fea, 2), (0x116fec, 3), (0x116fef, 2), (0x116ff1, 5), (0x116ff6, 3), (0x116ff9, 5), (0x116ffe, 3), (0x117001, 3), (0x117004, 2), (0x117006, 3), (0x117009, 3), (0x11700c, 5), (0x117011, 3), (0x117014, 3), (0x117017, 3), (0x11701a, 2), (0x11701c, 3), (0x11701f, 3), (0x117022, 2), (0x117024, 3), (0x117027, 3), (0x11702a, 3)]

theorem part28_layout [Bindings] : InstructionTrace.layout part28 = part28Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part28_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16f75 184 = part28Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
