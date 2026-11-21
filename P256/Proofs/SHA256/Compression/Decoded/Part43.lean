import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part43 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (add_m32_r32_effect_step 0x117ab6 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117aba 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117abd 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117abf 7 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117ac3 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ac5 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ac8 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117acb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ace 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117ad1 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ad3 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ad6 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117ad9 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117adb 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ade 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117ae1 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ae4 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ae7 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117aea 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117aed 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117af0 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117af3 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x117af6 0x34b0bcb5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117afb 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117afe 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b01 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b03 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b06 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b09 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b0b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117b0e 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b10 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b13 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117b16 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b19 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b1c 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b1f 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117b22 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b24 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b27 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117b2a 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b2c 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b2f 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117b31 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117b38 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117b3a 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b3d 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b3f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b42 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117b45 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117b49 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b4b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b4e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b51 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b53 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117b56 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117b59 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117b5b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b5e 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117b61 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117b64 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b67 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b6a 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117b6d 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part43Bytes : List UInt8 :=
  [0x1,0x6c,0x24,0x68,0xc1,0xed,0xa,0x31,0xcd,0x8b,0x7c,0x24,0x50,0x1,0xef,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe1,0x44,0x31,0xe9,0x44,0x21,0xf1,0x44,0x31,0xe9,0x41,0x1,0xf9,0x41,0x1,0xc9,0x44,0x89,0xd1,0xc1,0xc1,0x1e,0x44,0x1,0xc8,0x5,0xb5,0xbc,0xb0,0x34,0x44,0x89,0xd2,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xda,0x21,0xda,0x45,0x89,0xd9,0x41,0x31,0xd9,0x45,0x21,0xd1,0x41,0x31,0xd1,0x41,0x1,0xc9,0x41,0x1,0xc0,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc1,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x1,0xb4,0x24,0x80,0x0,0x0,0x0,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x8b,0x6c,0x24,0x78,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xe1,0x44,0x21,0xc1,0x44,0x31,0xe1,0x41,0x1,0xed,0x41,0x1,0xcd,0x44,0x1,0xe8]

set_option maxRecDepth 4096 in
theorem part43_bytes [Bindings] : part43.flatMap CheckedInstruction.bytes = part43Bytes  := by
  rfl

def part43Layout : List (BitVec 64 × Nat) :=
  [(0x117ab6, 4), (0x117aba, 3), (0x117abd, 2), (0x117abf, 4), (0x117ac3, 2), (0x117ac5, 3), (0x117ac8, 3), (0x117acb, 3), (0x117ace, 3), (0x117ad1, 2), (0x117ad3, 3), (0x117ad6, 3), (0x117ad9, 2), (0x117adb, 3), (0x117ade, 3), (0x117ae1, 3), (0x117ae4, 3), (0x117ae7, 3), (0x117aea, 3), (0x117aed, 3), (0x117af0, 3), (0x117af3, 3), (0x117af6, 5), (0x117afb, 3), (0x117afe, 3), (0x117b01, 2), (0x117b03, 3), (0x117b06, 3), (0x117b09, 2), (0x117b0b, 3), (0x117b0e, 2), (0x117b10, 3), (0x117b13, 3), (0x117b16, 3), (0x117b19, 3), (0x117b1c, 3), (0x117b1f, 3), (0x117b22, 2), (0x117b24, 3), (0x117b27, 3), (0x117b2a, 2), (0x117b2c, 3), (0x117b2f, 2), (0x117b31, 7), (0x117b38, 2), (0x117b3a, 3), (0x117b3d, 2), (0x117b3f, 3), (0x117b42, 3), (0x117b45, 4), (0x117b49, 2), (0x117b4b, 3), (0x117b4e, 3), (0x117b51, 2), (0x117b53, 3), (0x117b56, 3), (0x117b59, 2), (0x117b5b, 3), (0x117b5e, 3), (0x117b61, 3), (0x117b64, 3), (0x117b67, 3), (0x117b6a, 3), (0x117b6d, 3)]

theorem part43_layout [Bindings] : InstructionTrace.layout part43 = part43Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part43_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17ab6 186 = part43Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
