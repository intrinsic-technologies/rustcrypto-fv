import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part51 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11807e 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118081 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118083 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x118086 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118089 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11808c 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11808f 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x118092 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x118095 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x118098 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11809b 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11809e 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180a1 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180a4 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180a7 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180aa 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1180ad 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1180af 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1180b2 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180b4 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180b7 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180ba 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180bd 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1180c0 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180c2 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180c5 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1180c8 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1180ca 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1180cf 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1180d1 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180d4 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1180d7 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1180da 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1180dd 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1180e0 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1180e3 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x1180e5 0xc7 0xc67178f2 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180eb 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1180ee 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180f2 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1180f5 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1180f8 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1180fb 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1180fe 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x118102 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118105 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x118107 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11810a 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11810c 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11810f 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118112 0xdd rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_effect_step 0x118114 5 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11811b 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11811e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x118123 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x11812b 0 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x118132 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x11813a 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118142 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118144 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118146 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x118149 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x11814c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x118154 2 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part51Bytes : List UInt8 :=
  [0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xcb,0x44,0x21,0xdb,0x45,0x89,0xce,0x45,0x31,0xde,0x41,0x21,0xc6,0x41,0x31,0xde,0x41,0x1,0xee,0x41,0x1,0xfa,0x41,0x1,0xfe,0x44,0x89,0xfe,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xee,0xa,0x31,0xde,0x44,0x89,0xd7,0xc1,0xc7,0x1a,0x44,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x28,0x1,0xf3,0x44,0x1,0xc3,0x41,0x89,0xd0,0x41,0x31,0xc8,0x45,0x21,0xd0,0x41,0x31,0xc8,0x44,0x1,0xc3,0x1,0xdf,0x81,0xc7,0xf2,0x78,0x71,0xc6,0x45,0x89,0xf0,0x41,0xc1,0xc0,0x1e,0x44,0x89,0xf3,0xc1,0xc3,0x13,0x44,0x31,0xc3,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xd8,0x89,0xc3,0x44,0x21,0xcb,0x89,0xc5,0x44,0x31,0xcd,0x44,0x21,0xf5,0x31,0xdd,0x3,0xac,0x24,0xe8,0x0,0x0,0x0,0x44,0x1,0xc5,0x48,0x8b,0x74,0x24,0x18,0x44,0x3,0xb4,0x24,0xf8,0x0,0x0,0x0,0x3,0x84,0x24,0x8,0x1,0x0,0x0,0x44,0x3,0x8c,0x24,0x18,0x1,0x0,0x0,0x44,0x3,0x9c,0x24,0xf0,0x0,0x0,0x0,0x89,0xeb,0x1,0xfb,0x45,0x89,0xd8,0x41,0x1,0xf8,0x44,0x3,0x94,0x24,0x0,0x1,0x0,0x0,0x3,0x94,0x24,0x10,0x1,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part51_bytes [Bindings] : part51.flatMap CheckedInstruction.bytes = part51Bytes  := by
  rfl

def part51Layout : List (BitVec 64 × Nat) :=
  [(0x11807e, 3), (0x118081, 2), (0x118083, 3), (0x118086, 3), (0x118089, 3), (0x11808c, 3), (0x11808f, 3), (0x118092, 3), (0x118095, 3), (0x118098, 3), (0x11809b, 3), (0x11809e, 3), (0x1180a1, 3), (0x1180a4, 3), (0x1180a7, 3), (0x1180aa, 3), (0x1180ad, 2), (0x1180af, 3), (0x1180b2, 2), (0x1180b4, 3), (0x1180b7, 3), (0x1180ba, 3), (0x1180bd, 3), (0x1180c0, 2), (0x1180c2, 3), (0x1180c5, 3), (0x1180c8, 2), (0x1180ca, 5), (0x1180cf, 2), (0x1180d1, 3), (0x1180d4, 3), (0x1180d7, 3), (0x1180da, 3), (0x1180dd, 3), (0x1180e0, 3), (0x1180e3, 2), (0x1180e5, 6), (0x1180eb, 3), (0x1180ee, 4), (0x1180f2, 3), (0x1180f5, 3), (0x1180f8, 3), (0x1180fb, 3), (0x1180fe, 4), (0x118102, 3), (0x118105, 2), (0x118107, 3), (0x11810a, 2), (0x11810c, 3), (0x11810f, 3), (0x118112, 2), (0x118114, 7), (0x11811b, 3), (0x11811e, 5), (0x118123, 8), (0x11812b, 7), (0x118132, 8), (0x11813a, 8), (0x118142, 2), (0x118144, 2), (0x118146, 3), (0x118149, 3), (0x11814c, 8), (0x118154, 7)]

theorem part51_layout [Bindings] : InstructionTrace.layout part51 = part51Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part51_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1807e 221 = part51Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
