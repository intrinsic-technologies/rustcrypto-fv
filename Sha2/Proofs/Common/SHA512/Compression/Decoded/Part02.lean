import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part01
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part02 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de50 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de53 0x48 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10de57 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10de5a 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de5d 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10de60 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de63 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10de66 0x48 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10de69 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de6c 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 336)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10de74 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10de77 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de7a 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de7d 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10de81 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de84 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de87 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10de8b 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de8e 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de91 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10de95 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de98 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10de9b 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10de9e 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dea1 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10dea4 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dea7 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 328)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10deaf 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10deb2 0x4c (by simp [RexWPrefix]) 4 (.base 6 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10deb6 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10deb9 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10debd 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10dec2 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dec5 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dec9 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dece 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ded2 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ded7 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dedb 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dee0 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dee4 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dee9 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10deed 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10def2 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10def6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10defb 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10deff 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10df04 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10df08 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10df0d 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10df11 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10df16 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10df1a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part02Bytes : List UInt8 :=
  [0x48,0x89,0xda,0x48,0xc1,0xc2,0x17,0x48,0x31,0xc1,0x48,0x31,0xca,0x48,0x89,0xd9,0x48,0x21,0xe9,0x48,0x89,0xd8,0x48,0xf7,0xd0,0x4c,0x21,0xc0,0x4c,0x89,0x84,0x24,0x50,0x1,0x0,0x0,0x4c,0x1,0xe1,0x48,0x1,0xc1,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x24,0x48,0x1,0xd1,0x4c,0x89,0xda,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x4c,0x89,0xdf,0x48,0xc1,0xc7,0x19,0x48,0x31,0xd7,0x4c,0x89,0xfa,0x4c,0x31,0xf2,0x4c,0x21,0xda,0x4c,0x89,0xf8,0x4c,0x21,0xf0,0x4c,0x89,0xb4,0x24,0x48,0x1,0x0,0x0,0x48,0x31,0xd0,0x4c,0x8b,0x66,0x20,0x48,0x1,0xf8,0x48,0x8b,0x56,0x28,0x48,0x89,0x54,0x24,0x18,0x4c,0x1,0xc9,0x48,0x8b,0x56,0x30,0x48,0x89,0x54,0x24,0x20,0x48,0x8b,0x56,0x38,0x48,0x89,0x54,0x24,0x30,0x48,0x8b,0x56,0x40,0x48,0x89,0x54,0x24,0x68,0x48,0x8b,0x56,0x48,0x48,0x89,0x54,0x24,0x8,0x48,0x8b,0x56,0x50,0x48,0x89,0x54,0x24,0x10,0x48,0x8b,0x56,0x58,0x48,0x89,0x54,0x24,0x40,0x48,0x8b,0x56,0x60,0x48,0x89,0x54,0x24,0x28,0x48,0x8b,0x56,0x68,0x48,0x89,0x54,0x24,0x58,0x48,0x8b,0x56,0x70,0x48,0x89,0x54,0x24,0x60,0x48,0x8b,0x56,0x78,0x48,0x89,0x94,0x24,0x88,0x0,0x0,0x0]

def part02Layout : List (BitVec 64 × Nat) :=
  [(0x10de50, 3), (0x10de53, 4), (0x10de57, 3), (0x10de5a, 3), (0x10de5d, 3), (0x10de60, 3), (0x10de63, 3), (0x10de66, 3), (0x10de69, 3), (0x10de6c, 8), (0x10de74, 3), (0x10de77, 3), (0x10de7a, 3), (0x10de7d, 4), (0x10de81, 3), (0x10de84, 3), (0x10de87, 4), (0x10de8b, 3), (0x10de8e, 3), (0x10de91, 4), (0x10de95, 3), (0x10de98, 3), (0x10de9b, 3), (0x10de9e, 3), (0x10dea1, 3), (0x10dea4, 3), (0x10dea7, 8), (0x10deaf, 3), (0x10deb2, 4), (0x10deb6, 3), (0x10deb9, 4), (0x10debd, 5), (0x10dec2, 3), (0x10dec5, 4), (0x10dec9, 5), (0x10dece, 4), (0x10ded2, 5), (0x10ded7, 4), (0x10dedb, 5), (0x10dee0, 4), (0x10dee4, 5), (0x10dee9, 4), (0x10deed, 5), (0x10def2, 4), (0x10def6, 5), (0x10defb, 4), (0x10deff, 5), (0x10df04, 4), (0x10df08, 5), (0x10df0d, 4), (0x10df11, 5), (0x10df16, 4), (0x10df1a, 8)]

set_option maxRecDepth 32768 in
theorem part02_bytes [Bindings] : part02.flatMap CheckedInstruction.bytes = part02Bytes := by
  rfl

set_option maxRecDepth 32768 in
theorem part02_layout [Bindings] : InstructionTrace.layout part02 = part02Layout := by
  rfl

theorem part02_ordered [Bindings] : InstructionTrace.ordered 0x10de50 part02 = true := by
  rw [InstructionTrace.ordered_eq_layout, part02_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part02_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xde50 210 = part02Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
