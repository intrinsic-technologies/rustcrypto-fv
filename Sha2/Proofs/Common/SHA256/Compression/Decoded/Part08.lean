import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part08 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb43 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10bb46 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb48 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb4b 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10bb4e 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bb52 0xc1 0x72be5d74 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb58 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb5a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb5d 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb5f 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb62 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb64 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb66 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb69 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb6b 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bb6e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb70 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb73 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb76 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb79 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb7c 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bb7f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb81 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb84 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb86 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb89 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb8b 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb8e 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb90 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb92 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb95 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bb97 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bb9c 7 (.base 6 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10bb9f 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bba1 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bba5 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bba7 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbaa 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbad 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbb0 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10bbb2 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bbb4 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbb7 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbba 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbbd 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbc0 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bbc3 0xc1 0x80deb1fe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbc9 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbcc 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bbcf 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbd1 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbd4 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bbd7 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbd9 0xdf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bbdb 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbde 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbe1 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bbe4 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbe7 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbea 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bbed 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbef 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbf1 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbf4 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part08Bytes : List UInt8 :=
  [0x44,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xc1,0x41,0x1,0xc9,0x42,0x8d,0xc,0xe,0x81,0xc1,0x74,0x5d,0xbe,0x72,0x89,0xde,0xc1,0xc6,0x1e,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x89,0xde,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xff,0x21,0xd7,0x45,0x89,0xf9,0x41,0x31,0xd1,0x41,0x21,0xd9,0x41,0x31,0xf9,0x41,0x1,0xf1,0x1,0xc8,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0x1a,0x89,0xc6,0xc1,0xc6,0x15,0x31,0xce,0x89,0xc1,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x7e,0x34,0xf,0xcf,0x89,0x7c,0x24,0x10,0x89,0xc6,0x44,0x21,0xd6,0x41,0x1,0xf8,0x41,0x1,0xf0,0x89,0xc6,0xf7,0xd6,0x44,0x21,0xde,0x41,0x1,0xf0,0x44,0x89,0xce,0xc1,0xc6,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xfe,0xb1,0xde,0x80,0x44,0x89,0xcf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xce,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xdf,0x44,0x21,0xff,0x41,0x89,0xde,0x45,0x31,0xfe,0x45,0x21,0xce,0x41,0x31,0xfe,0x41,0x1,0xf6,0x1,0xca,0x89,0xd6,0xc1,0xc6,0x1a,0x41,0x1,0xce]

set_option maxRecDepth 4096 in
theorem part08_bytes [Bindings] : part08.flatMap CheckedInstruction.bytes = part08Bytes  := by
  rfl

def part08Layout : List (BitVec 64 × Nat) :=
  [(0x10bb43, 3), (0x10bb46, 2), (0x10bb48, 3), (0x10bb4b, 3), (0x10bb4e, 4), (0x10bb52, 6), (0x10bb58, 2), (0x10bb5a, 3), (0x10bb5d, 2), (0x10bb5f, 3), (0x10bb62, 2), (0x10bb64, 2), (0x10bb66, 3), (0x10bb69, 2), (0x10bb6b, 3), (0x10bb6e, 2), (0x10bb70, 3), (0x10bb73, 3), (0x10bb76, 3), (0x10bb79, 3), (0x10bb7c, 3), (0x10bb7f, 2), (0x10bb81, 3), (0x10bb84, 2), (0x10bb86, 3), (0x10bb89, 2), (0x10bb8b, 3), (0x10bb8e, 2), (0x10bb90, 2), (0x10bb92, 3), (0x10bb95, 2), (0x10bb97, 5), (0x10bb9c, 3), (0x10bb9f, 2), (0x10bba1, 4), (0x10bba5, 2), (0x10bba7, 3), (0x10bbaa, 3), (0x10bbad, 3), (0x10bbb0, 2), (0x10bbb2, 2), (0x10bbb4, 3), (0x10bbb7, 3), (0x10bbba, 3), (0x10bbbd, 3), (0x10bbc0, 3), (0x10bbc3, 6), (0x10bbc9, 3), (0x10bbcc, 3), (0x10bbcf, 2), (0x10bbd1, 3), (0x10bbd4, 3), (0x10bbd7, 2), (0x10bbd9, 2), (0x10bbdb, 3), (0x10bbde, 3), (0x10bbe1, 3), (0x10bbe4, 3), (0x10bbe7, 3), (0x10bbea, 3), (0x10bbed, 2), (0x10bbef, 2), (0x10bbf1, 3), (0x10bbf4, 3)]

theorem part08_layout [Bindings] : InstructionTrace.layout part08 = part08Layout := by
  rfl

theorem part08_ordered [Bindings] : InstructionTrace.ordered 0x10bb43 part08 = true := by
  rw [InstructionTrace.ordered_eq_layout, part08_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part08_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbb43 180 = part08Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
