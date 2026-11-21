import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part10

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part11 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e1fa 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1e2f) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e201 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e204 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e207 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e20a 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e20d 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e210 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e213 0x49 0xd1 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e216 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e219 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e21c 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e220 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e223 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e226 0x49 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e22a 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e22d 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e230 0x49 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e234 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e237 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e23a 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e23d 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e240 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e243 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e246 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e249 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e24c 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e24f 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e252 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e256 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e259 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e25c 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e260 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e263 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e266 0x49 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e26a 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e26d 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e270 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e275 12) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e278 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part11Bytes : List UInt8 :=
  [0x48,0x8b,0xd,0x2f,0x1e,0xf,0x0,0x48,0x1,0xe9,0x4c,0x1,0xc9,0x49,0x89,0xd9,0x49,0x21,0xc1,0x4c,0x1,0xc9,0x49,0x89,0xd9,0x49,0xf7,0xd1,0x49,0x21,0xd1,0x4d,0x89,0xc6,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xc9,0x4d,0x89,0xc1,0x49,0xc1,0xc1,0x1e,0x4c,0x1,0xd1,0x4d,0x89,0xc2,0x49,0xc1,0xc2,0x19,0x4d,0x31,0xf1,0x4d,0x31,0xca,0x49,0x89,0xfe,0x4d,0x21,0xde,0x49,0x89,0xf9,0x4d,0x31,0xd9,0x4d,0x21,0xc1,0x4d,0x31,0xf1,0x48,0x1,0xce,0x49,0x89,0xf6,0x49,0xc1,0xc6,0x32,0x4d,0x1,0xd1,0x49,0x89,0xf7,0x49,0xc1,0xc7,0x2e,0x49,0x1,0xc9,0x49,0x89,0xf2,0x49,0xc1,0xc2,0x17,0x4d,0x31,0xf7,0x4d,0x31,0xfa,0x4c,0x8b,0x64,0x24,0x30,0x49,0xf,0xcc,0x4c,0x89,0x64,0x24,0x30]

def part11Layout : List (BitVec 64 × Nat) :=
  [(0x10e1fa, 7), (0x10e201, 3), (0x10e204, 3), (0x10e207, 3), (0x10e20a, 3),
   (0x10e20d, 3), (0x10e210, 3), (0x10e213, 3), (0x10e216, 3), (0x10e219, 3),
   (0x10e21c, 4), (0x10e220, 3), (0x10e223, 3), (0x10e226, 4), (0x10e22a, 3),
   (0x10e22d, 3), (0x10e230, 4), (0x10e234, 3), (0x10e237, 3), (0x10e23a, 3),
   (0x10e23d, 3), (0x10e240, 3), (0x10e243, 3), (0x10e246, 3), (0x10e249, 3),
   (0x10e24c, 3), (0x10e24f, 3), (0x10e252, 4), (0x10e256, 3), (0x10e259, 3),
   (0x10e25c, 4), (0x10e260, 3), (0x10e263, 3), (0x10e266, 4), (0x10e26a, 3),
   (0x10e26d, 3), (0x10e270, 5), (0x10e275, 3), (0x10e278, 5)]

set_option maxRecDepth 4096 in
theorem part11_bytes [Bindings] : part11.flatMap CheckedInstruction.bytes = part11Bytes := by
  rfl

theorem part11_layout [Bindings] : InstructionTrace.layout part11 = part11Layout := by
  rfl

theorem part11_ordered [Bindings] : InstructionTrace.ordered 0x10e1fa part11 = true := by
  rw [InstructionTrace.ordered_eq_layout, part11_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part11_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe1fa 131 = part11Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
