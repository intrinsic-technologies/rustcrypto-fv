import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part07

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part08 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e074 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10e077 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1f9a) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e07e 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e081 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e084 0x48 0xd7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e087 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e08a 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e08d 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e090 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e093 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e097 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e09a 0x49 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e09e 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0a1 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e0a4 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e0a8 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0ab 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e0ae 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0b1 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e0b4 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 304)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0bc 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e0bf 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e0c2 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e0c5 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e0c8 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e0cb 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e0ce 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0d1 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e0d4 0x49 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0d8 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e0db 0x49 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e0df 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e0e2 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e0e6 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e0e9 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e0ec 12) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e0ef 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part08Bytes : List UInt8 :=
  [0x4c,0x1,0xf2,0x48,0x3,0x15,0x9a,0x1f,0xf,0x0,0x48,0x1,0xfa,0x4c,0x89,0xcf,0x48,0xf7,0xd7,0x48,0x21,0xcf,0x48,0x1,0xfa,0x4c,0x1,0xd2,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x24,0x49,0x89,0xf2,0x49,0xc1,0xc2,0x1e,0x49,0x31,0xfa,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x19,0x4c,0x31,0xd7,0x49,0x89,0xda,0x49,0x21,0xc2,0x4d,0x89,0xde,0x4c,0x89,0x9c,0x24,0x30,0x1,0x0,0x0,0x49,0x89,0xdb,0x49,0x31,0xc3,0x49,0x21,0xf3,0x4d,0x31,0xd3,0x49,0x1,0xfb,0x49,0x1,0xd3,0x4c,0x1,0xf2,0x49,0x89,0xd2,0x49,0xc1,0xc2,0x32,0x49,0x89,0xd6,0x49,0xc1,0xc6,0x2e,0x48,0x89,0xd7,0x48,0xc1,0xc7,0x17,0x4d,0x31,0xd6,0x4c,0x31,0xf7,0x49,0xf,0xcc,0x4c,0x89,0xa4,0x24,0xa8,0x0,0x0,0x0]

def part08Layout : List (BitVec 64 × Nat) :=
  [(0x10e074, 3), (0x10e077, 7), (0x10e07e, 3), (0x10e081, 3), (0x10e084, 3),
   (0x10e087, 3), (0x10e08a, 3), (0x10e08d, 3), (0x10e090, 3), (0x10e093, 4),
   (0x10e097, 3), (0x10e09a, 4), (0x10e09e, 3), (0x10e0a1, 3), (0x10e0a4, 4),
   (0x10e0a8, 3), (0x10e0ab, 3), (0x10e0ae, 3), (0x10e0b1, 3), (0x10e0b4, 8),
   (0x10e0bc, 3), (0x10e0bf, 3), (0x10e0c2, 3), (0x10e0c5, 3), (0x10e0c8, 3),
   (0x10e0cb, 3), (0x10e0ce, 3), (0x10e0d1, 3), (0x10e0d4, 4), (0x10e0d8, 3),
   (0x10e0db, 4), (0x10e0df, 3), (0x10e0e2, 4), (0x10e0e6, 3), (0x10e0e9, 3),
   (0x10e0ec, 3), (0x10e0ef, 8)]

set_option maxRecDepth 4096 in
theorem part08_bytes [Bindings] : part08.flatMap CheckedInstruction.bytes = part08Bytes := by
  rfl

theorem part08_layout [Bindings] : InstructionTrace.layout part08 = part08Layout := by
  rfl

theorem part08_ordered [Bindings] : InstructionTrace.ordered 0x10e074 part08 = true := by
  rw [InstructionTrace.ordered_eq_layout, part08_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part08_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe074 131 = part08Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
