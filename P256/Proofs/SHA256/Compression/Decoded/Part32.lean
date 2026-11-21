import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part32 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117251 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117255 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117258 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x11725b 0x41 0xeb 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11725f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117262 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117266 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x117269 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11726e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x117271 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117275 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117278 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11727b 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x11727e 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117282 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117285 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117288 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11728c 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11728f 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117292 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117295 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117298 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11729b 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11729e 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1172a1 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1172a4 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1172a7 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1172aa 0x46 (by simp [RexNoWPrefix]) 3 (.sib 2 (some 13) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x1172ae 0x41 0xc3 0x81c2c92e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1172b5 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1172b7 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172ba 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1172bd 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1172c1 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172c4 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1172c7 0x41 0xc7 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1172cb 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172ce 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1172d1 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1172d4 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1172d6 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1172d8 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1172da 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172dd 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1172e0 0xc3 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1172e3 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172e6 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1172e9 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1172ed 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172f0 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1172f3 0x41 0xc7 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1172f7 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1172fa 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1172fd 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117301 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117304 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117307 0xeb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117309 0xeb 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11730c 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x11730f 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117314 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117317 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11731a 3 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11731e 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part32Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0xe,0x45,0x31,0xd9,0x45,0x89,0xe3,0x41,0xc1,0xeb,0x3,0x45,0x31,0xcb,0x1,0x5c,0x24,0x58,0x41,0x1,0xdb,0x44,0x89,0x5c,0x24,0x78,0x41,0x89,0xd9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x14,0x44,0x1,0xcd,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x7,0x44,0x31,0xca,0x41,0x89,0xc9,0x45,0x31,0xc1,0x45,0x21,0xd1,0x45,0x31,0xc1,0x41,0x1,0xed,0x45,0x1,0xcd,0x46,0x8d,0x1c,0x2a,0x41,0x81,0xc3,0x2e,0xc9,0xc2,0x81,0x89,0xf2,0xc1,0xc2,0x1e,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x13,0x41,0x31,0xd1,0x41,0x89,0xf7,0x41,0xc1,0xc7,0xa,0x45,0x31,0xcf,0x41,0x89,0xc1,0x41,0x21,0xf9,0x89,0xc2,0x31,0xfa,0x21,0xf2,0x44,0x31,0xca,0x44,0x89,0xe3,0xc1,0xc3,0xf,0x44,0x1,0xfa,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xd,0x45,0x1,0xde,0x41,0x89,0xef,0x41,0xc1,0xc7,0x19,0x44,0x1,0xda,0x41,0x89,0xeb,0x41,0xc1,0xc3,0xe,0x41,0x31,0xd9,0x45,0x31,0xfb,0x89,0xeb,0xc1,0xeb,0x3,0x44,0x31,0xdb,0x44,0x8b,0x6c,0x24,0x10,0x45,0x1,0xe5,0x44,0x1,0xe3,0x89,0x5c,0x24,0x14,0x45,0x89,0xe3]

set_option maxRecDepth 4096 in
theorem part32_bytes [Bindings] : part32.flatMap CheckedInstruction.bytes = part32Bytes  := by
  rfl

def part32Layout : List (BitVec 64 × Nat) :=
  [(0x117251, 4), (0x117255, 3), (0x117258, 3), (0x11725b, 4), (0x11725f, 3), (0x117262, 4), (0x117266, 3), (0x117269, 5), (0x11726e, 3), (0x117271, 4), (0x117275, 3), (0x117278, 3), (0x11727b, 3), (0x11727e, 4), (0x117282, 3), (0x117285, 3), (0x117288, 4), (0x11728c, 3), (0x11728f, 3), (0x117292, 3), (0x117295, 3), (0x117298, 3), (0x11729b, 3), (0x11729e, 3), (0x1172a1, 3), (0x1172a4, 3), (0x1172a7, 3), (0x1172aa, 4), (0x1172ae, 7), (0x1172b5, 2), (0x1172b7, 3), (0x1172ba, 3), (0x1172bd, 4), (0x1172c1, 3), (0x1172c4, 3), (0x1172c7, 4), (0x1172cb, 3), (0x1172ce, 3), (0x1172d1, 3), (0x1172d4, 2), (0x1172d6, 2), (0x1172d8, 2), (0x1172da, 3), (0x1172dd, 3), (0x1172e0, 3), (0x1172e3, 3), (0x1172e6, 3), (0x1172e9, 4), (0x1172ed, 3), (0x1172f0, 3), (0x1172f3, 4), (0x1172f7, 3), (0x1172fa, 3), (0x1172fd, 4), (0x117301, 3), (0x117304, 3), (0x117307, 2), (0x117309, 3), (0x11730c, 3), (0x11730f, 5), (0x117314, 3), (0x117317, 3), (0x11731a, 4), (0x11731e, 3)]

theorem part32_layout [Bindings] : InstructionTrace.layout part32 = part32Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part32_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17251 208 = part32Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
