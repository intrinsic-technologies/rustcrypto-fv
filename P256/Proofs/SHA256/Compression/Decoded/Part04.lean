import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part04 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d1d 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115d20 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d23 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d26 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115d29 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d2b 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d2e 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d32 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115d35 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115d37 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d3a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d3d 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d40 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d44 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115d47 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115d4c 5 (.base 2 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115d4f 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115d51 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115d55 0xca rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115d57 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d59 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d5c 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115d5f 0xca rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115d61 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115d63 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d65 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115d68 0x43 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115d6c 0xc2 0x923f82a4 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d72 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d75 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d79 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d7c 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d80 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d83 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115d86 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d8a 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d8d 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115d90 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115d92 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d95 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115d98 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115d9b 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115d9e 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115da1 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115da3 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115da6 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115da8 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115dab 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115dae 0x41 0xc2 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115db2 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115db5 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115db7 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115dba 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115dbd 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x115dc2 0x41 (by simp [RexNoWPrefix]) 5 (.base 10 (.d8 28)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115dc6 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115dc8 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115dcc 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115dcf 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115dd2 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115dd4 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115dd7 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x115dda 0x41 0xd2 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ddd 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part04Bytes : List UInt8 :=
  [0x41,0x31,0xf0,0x45,0x21,0xc8,0x41,0x31,0xe8,0x45,0x1,0xd8,0x1,0xd1,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x1a,0x41,0x1,0xd0,0x89,0xca,0xc1,0xc2,0x15,0x44,0x31,0xda,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x18,0xf,0xcd,0x89,0x6c,0x24,0x28,0x89,0xca,0x21,0xc2,0x41,0x1,0xea,0x41,0x1,0xd2,0x89,0xca,0xf7,0xd2,0x21,0xda,0x41,0x1,0xd2,0x43,0x8d,0x14,0x13,0x81,0xc2,0xa4,0x82,0x3f,0x92,0x45,0x89,0xc2,0x41,0xc1,0xc2,0x1e,0x45,0x89,0xc3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x45,0x89,0xc2,0x41,0xc1,0xc2,0xa,0x45,0x31,0xda,0x44,0x89,0xcd,0x21,0xfd,0x45,0x89,0xcb,0x41,0x31,0xfb,0x45,0x21,0xc3,0x41,0x31,0xeb,0x45,0x1,0xd3,0x1,0xd6,0x41,0x1,0xd3,0x89,0xf2,0xc1,0xc2,0x1a,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x15,0x41,0x31,0xd2,0x89,0xf2,0xc1,0xc2,0x7,0x44,0x31,0xd2,0x4c,0x8b,0x54,0x24,0x18,0x41,0x8b,0x6a,0x1c,0xf,0xcd,0x89,0x6c,0x24,0x14,0x41,0x89,0xf2,0x41,0x21,0xca,0x1,0xeb,0x44,0x1,0xd3,0x41,0x89,0xf2,0x41,0xf7,0xd2,0x41,0x21,0xc2]

set_option maxRecDepth 4096 in
theorem part04_bytes [Bindings] : part04.flatMap CheckedInstruction.bytes = part04Bytes  := by
  rfl

def part04Layout : List (BitVec 64 × Nat) :=
  [(0x115d1d, 3), (0x115d20, 3), (0x115d23, 3), (0x115d26, 3), (0x115d29, 2), (0x115d2b, 3), (0x115d2e, 4), (0x115d32, 3), (0x115d35, 2), (0x115d37, 3), (0x115d3a, 3), (0x115d3d, 3), (0x115d40, 4), (0x115d44, 3), (0x115d47, 5), (0x115d4c, 3), (0x115d4f, 2), (0x115d51, 4), (0x115d55, 2), (0x115d57, 2), (0x115d59, 3), (0x115d5c, 3), (0x115d5f, 2), (0x115d61, 2), (0x115d63, 2), (0x115d65, 3), (0x115d68, 4), (0x115d6c, 6), (0x115d72, 3), (0x115d75, 4), (0x115d79, 3), (0x115d7c, 4), (0x115d80, 3), (0x115d83, 3), (0x115d86, 4), (0x115d8a, 3), (0x115d8d, 3), (0x115d90, 2), (0x115d92, 3), (0x115d95, 3), (0x115d98, 3), (0x115d9b, 3), (0x115d9e, 3), (0x115da1, 2), (0x115da3, 3), (0x115da6, 2), (0x115da8, 3), (0x115dab, 3), (0x115dae, 4), (0x115db2, 3), (0x115db5, 2), (0x115db7, 3), (0x115dba, 3), (0x115dbd, 5), (0x115dc2, 4), (0x115dc6, 2), (0x115dc8, 4), (0x115dcc, 3), (0x115dcf, 3), (0x115dd2, 2), (0x115dd4, 3), (0x115dd7, 3), (0x115dda, 3), (0x115ddd, 3)]

theorem part04_layout [Bindings] : InstructionTrace.layout part04 = part04Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part04_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15d1d 195 = part04Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
