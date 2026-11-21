import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part13

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part14 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e383 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1cbe) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e38a 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e38d 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e390 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e393 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e396 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e399 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e39c 0x48 0xd3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e39f 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3a2 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3a5 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e3a9 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3ac 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3af 0x48 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e3b3 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3b6 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3b9 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3bd 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3c0 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3c3 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e3c6 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3c9 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3cc 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e3cf 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3d2 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e3d5 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3d8 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3db 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e3df 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3e2 0x4d 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3e5 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e3e9 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e3ec 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e3ef 0x48 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3f3 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e3f6 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e3f9 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e3fe 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e401 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part14Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0xbe,0x1c,0xf,0x0,0x4c,0x1,0xf2,0x48,0x1,0xda,0x48,0x89,0xfb,0x4c,0x21,0xdb,0x48,0x1,0xda,0x48,0x89,0xfb,0x48,0xf7,0xd3,0x48,0x21,0xf3,0x49,0x89,0xce,0x49,0xc1,0xc6,0x24,0x48,0x1,0xda,0x48,0x89,0xcb,0x48,0xc1,0xc3,0x1e,0x48,0x1,0xc2,0x49,0x89,0xcf,0x49,0xc1,0xc7,0x19,0x4c,0x31,0xf3,0x49,0x31,0xdf,0x4c,0x89,0xd3,0x4c,0x21,0xcb,0x4c,0x89,0xd0,0x4c,0x31,0xc8,0x48,0x21,0xc8,0x48,0x31,0xd8,0x49,0x1,0xd0,0x4d,0x89,0xc6,0x49,0xc1,0xc6,0x32,0x4c,0x1,0xf8,0x4d,0x89,0xc7,0x49,0xc1,0xc7,0x2e,0x48,0x1,0xd0,0x4c,0x89,0xc3,0x48,0xc1,0xc3,0x17,0x4d,0x31,0xf7,0x4c,0x31,0xfb,0x4c,0x8b,0x74,0x24,0x10,0x49,0xf,0xce,0x4c,0x89,0x74,0x24,0x10]

def part14Layout : List (BitVec 64 × Nat) :=
  [(0x10e383, 7), (0x10e38a, 3), (0x10e38d, 3), (0x10e390, 3), (0x10e393, 3),
   (0x10e396, 3), (0x10e399, 3), (0x10e39c, 3), (0x10e39f, 3), (0x10e3a2, 3),
   (0x10e3a5, 4), (0x10e3a9, 3), (0x10e3ac, 3), (0x10e3af, 4), (0x10e3b3, 3),
   (0x10e3b6, 3), (0x10e3b9, 4), (0x10e3bd, 3), (0x10e3c0, 3), (0x10e3c3, 3),
   (0x10e3c6, 3), (0x10e3c9, 3), (0x10e3cc, 3), (0x10e3cf, 3), (0x10e3d2, 3),
   (0x10e3d5, 3), (0x10e3d8, 3), (0x10e3db, 4), (0x10e3df, 3), (0x10e3e2, 3),
   (0x10e3e5, 4), (0x10e3e9, 3), (0x10e3ec, 3), (0x10e3ef, 4), (0x10e3f3, 3),
   (0x10e3f6, 3), (0x10e3f9, 5), (0x10e3fe, 3), (0x10e401, 5)]

set_option maxRecDepth 4096 in
theorem part14_bytes [Bindings] : part14.flatMap CheckedInstruction.bytes = part14Bytes := by
  rfl

theorem part14_layout [Bindings] : InstructionTrace.layout part14 = part14Layout := by
  rfl

theorem part14_ordered [Bindings] : InstructionTrace.ordered 0x10e383 part14 = true := by
  rw [InstructionTrace.ordered_eq_layout, part14_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part14_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe383 131 = part14Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
