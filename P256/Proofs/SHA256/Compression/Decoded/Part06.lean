import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part06 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e93 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e96 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e99 0xda rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115e9b 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115ea0 5 (.base 3 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115ea3 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115ea5 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ea9 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115eac 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115eae 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115eb0 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115eb2 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115eb5 0xd3 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115eb7 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115eb9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115ebb 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115ebd 0xc3 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115ec0 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115ec2 0xc1 0x12835b01 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115ec8 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115eca 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115ecd 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115ecf 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115ed1 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115ed4 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ed6 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115ed9 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115edc 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115edf 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115ee2 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115ee4 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115ee6 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115ee8 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115eeb 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115eee 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115ef1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115ef3 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115ef6 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115ef9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115efb 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115efe 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115f01 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115f03 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115f08 5 (.base 1 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115f0b 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115f0d 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f11 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115f14 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f17 0xee rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f19 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115f1b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115f1e 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115f20 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115f22 0xce rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x115f24 1 (.sib 3 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115f27 0xc1 0x243185be rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115f2d 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f2f 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115f32 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f34 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115f37 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115f39 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115f3b 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115f3e 0xde rfl) (by x86_local)]

def part06Bytes : List UInt8 :=
  [0x44,0x89,0xca,0xc1,0xc2,0x7,0x31,0xda,0x48,0x8b,0x5c,0x24,0x18,0x8b,0x6b,0x24,0xf,0xcd,0x89,0x6c,0x24,0x8,0x44,0x89,0xcb,0x21,0xfb,0x1,0xe9,0x1,0xd9,0x44,0x89,0xcb,0xf7,0xd3,0x21,0xf3,0x1,0xd9,0x89,0xc3,0xc1,0xc3,0x1e,0x1,0xd1,0x81,0xc1,0x1,0x5b,0x83,0x12,0x89,0xc2,0xc1,0xc2,0x13,0x31,0xda,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xd3,0x44,0x89,0xd5,0x44,0x21,0xdd,0x44,0x89,0xd2,0x44,0x31,0xda,0x21,0xc2,0x31,0xea,0x1,0xda,0x41,0x1,0xc8,0x44,0x89,0xc3,0xc1,0xc3,0x1a,0x1,0xca,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xd9,0x44,0x89,0xc3,0xc1,0xc3,0x7,0x31,0xcb,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x28,0xf,0xcd,0x89,0x6c,0x24,0xc,0x44,0x89,0xc1,0x44,0x21,0xc9,0x1,0xee,0x1,0xce,0x44,0x89,0xc1,0xf7,0xd1,0x21,0xf9,0x1,0xce,0x8d,0xc,0x33,0x81,0xc1,0xbe,0x85,0x31,0x24,0x89,0xd6,0xc1,0xc6,0x1e,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xd6,0xc1,0xc6,0xa,0x31,0xde]

set_option maxRecDepth 4096 in
theorem part06_bytes [Bindings] : part06.flatMap CheckedInstruction.bytes = part06Bytes  := by
  rfl

def part06Layout : List (BitVec 64 × Nat) :=
  [(0x115e93, 3), (0x115e96, 3), (0x115e99, 2), (0x115e9b, 5), (0x115ea0, 3), (0x115ea3, 2), (0x115ea5, 4), (0x115ea9, 3), (0x115eac, 2), (0x115eae, 2), (0x115eb0, 2), (0x115eb2, 3), (0x115eb5, 2), (0x115eb7, 2), (0x115eb9, 2), (0x115ebb, 2), (0x115ebd, 3), (0x115ec0, 2), (0x115ec2, 6), (0x115ec8, 2), (0x115eca, 3), (0x115ecd, 2), (0x115ecf, 2), (0x115ed1, 3), (0x115ed4, 2), (0x115ed6, 3), (0x115ed9, 3), (0x115edc, 3), (0x115edf, 3), (0x115ee2, 2), (0x115ee4, 2), (0x115ee6, 2), (0x115ee8, 3), (0x115eeb, 3), (0x115eee, 3), (0x115ef1, 2), (0x115ef3, 3), (0x115ef6, 3), (0x115ef9, 2), (0x115efb, 3), (0x115efe, 3), (0x115f01, 2), (0x115f03, 5), (0x115f08, 3), (0x115f0b, 2), (0x115f0d, 4), (0x115f11, 3), (0x115f14, 3), (0x115f17, 2), (0x115f19, 2), (0x115f1b, 3), (0x115f1e, 2), (0x115f20, 2), (0x115f22, 2), (0x115f24, 3), (0x115f27, 6), (0x115f2d, 2), (0x115f2f, 3), (0x115f32, 2), (0x115f34, 3), (0x115f37, 2), (0x115f39, 2), (0x115f3b, 3), (0x115f3e, 2)]

theorem part06_layout [Bindings] : InstructionTrace.layout part06 = part06Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part06_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15e93 173 = part06Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
