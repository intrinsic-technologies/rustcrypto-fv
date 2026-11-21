import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Finalize.Store8
import Md5.Proofs.Buffered.Xor
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] relocated

def paddingBytes : List UInt8 :=
  [0x4c, 0x89, 0xfb, 0x48, 0x83, 0xf3, 0x3f, 0x42, 0xc6, 0x44, 0x3c, 0x10, 0x80,
    0x4a, 0x8d, 0x3c, 0x3c, 0x48, 0x83, 0xc7, 0x11, 0x31, 0xf6, 0x48, 0x89, 0xda]

structure PaddingPre (s : RamState) (update : Bool := false) : Prop extends Storage (streamKind update) s where
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x100463))
  positionBound : ((.reg 15 : Operand 64).read s).toNat < 64

def paddingEffect (s : RamState) (update : Bool := false) : Effect :=
  let pos := (.reg 15 : Operand 64).read s
  { rip := (BitVec.ofNat 64 (relocated update 0x10047d))
    writes := [⟨(.reg 3 : Operand 64), pos ^^^ 63⟩,
      ⟨(.mem (stackPtr s + pos + 16) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + 17⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), pos ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 600000 in
theorem padding_execution {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PaddingPre (update := update)) (codeRange (BitVec.ofNat 64 (relocated update 0x100463)) paddingBytes) (paddingEffect (update := update)) := by
  cases update
  case false =>
    unfold paddingBytes
    md5_run_begin (mov_r64_r64_effect_step (BitVec.ofNat 64 0x100463) 0x4c 0xfb
      (by unfold RexWPrefix; decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x466 (by decide +kernel)
    md5_run_then (xor_r64_imm8_effect_step (BitVec.ofNat 64 0x100466) 0x48 0xf3 63
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x46a (by decide +kernel)
    md5_run_then (mov_m8_imm8_rex_effect_step (BitVec.ofNat 64 0x10046a) 0x42
      (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 16))
      (by decide) (by decide) (by decide) 128)
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 7 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hs : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have hp : (.reg 15 : Operand 64).read t = (.reg 15 : Operand 64).read s :=
        hE.agrees.read (by x86_norm)
      have hw := h.toStorage.stackWritable (((.reg 15 : Operand 64).read s).toNat + 16) 1
        (by have := h.positionBound; change _ ≤ 280; omega)
      have hc (off len : Nat) (hcode : off + len ≤ Extracted.textBytes.size) :=
        h.toStorage.stackApart (offset := ((.reg 15 : Operand 64).read s).toNat + 16)
          (len := 1) (codeOffset := off) (codeLen := len)
          (by have := h.positionBound; change _ ≤ 280; omega) hcode
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm [BitVec.shiftLeft_zero]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hw
      · x86_norm [BitVec.shiftLeft_zero]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hc 0x46a 6 (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip (show
          (movM8Imm8RexEffect (BitVec.ofNat 64 0x10046a) (.sib 4 (some 15) 0 (.d8 16)) 128 t).components =
            [.mem (stackPtr t + (.reg 15 : Operand 64).read t + 16) 1, .rip] by
          x86_norm [BitVec.shiftLeft_zero, stackPtr]; rfl)
        rw [hs, hp]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hc 0x463 26 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x470 (by decide +kernel)
    md5_run_then (lea_r64_effect_step (BitVec.ofNat 64 0x100470) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x474 (by decide +kernel)
    md5_run_then (add_r64_imm8_effect_step (BitVec.ofNat 64 0x100474) 0x48 0xc7 17
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 17 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x478 (by decide +kernel)
    md5_run_then (xor_r32_r32_effect_step (BitVec.ofNat 64 0x100478) 0xf6 (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 21 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x47a (by decide +kernel)
    md5_run_then (mov_r64_r64_effect_step (BitVec.ofNat 64 0x10047a) 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100463)) 23 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x47d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [paddingEffect]
    · x86_norm [paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
      simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
    · intro i; cases i <;> x86_norm [paddingEffect]
    · x86_norm [paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
      simp [Operand.read]

  case true =>
    unfold paddingBytes
    md5_run_begin (mov_r64_r64_effect_step (BitVec.ofNat 64 0x101a13) 0x4c 0xfb
      (by unfold RexWPrefix; decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a16 (by decide +kernel)
    md5_run_then (xor_r64_imm8_effect_step (BitVec.ofNat 64 0x101a16) 0x48 0xf3 63
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a1a (by decide +kernel)
    md5_run_then (mov_m8_imm8_rex_effect_step (BitVec.ofNat 64 0x101a1a) 0x42
      (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 16))
      (by decide) (by decide) (by decide) 128)
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 7 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hs : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have hp : (.reg 15 : Operand 64).read t = (.reg 15 : Operand 64).read s :=
        hE.agrees.read (by x86_norm)
      have hw := h.toStorage.stackWritable (((.reg 15 : Operand 64).read s).toNat + 16) 1
        (by have := h.positionBound; change _ ≤ 280; omega)
      have hc (off len : Nat) (hcode : off + len ≤ Extracted.textBytes.size) :=
        h.toStorage.stackApart (offset := ((.reg 15 : Operand 64).read s).toNat + 16)
          (len := 1) (codeOffset := off) (codeLen := len)
          (by have := h.positionBound; change _ ≤ 280; omega) hcode
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm [BitVec.shiftLeft_zero]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hw
      · x86_norm [BitVec.shiftLeft_zero]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hc 0x1a1a 6 (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip (show
          (movM8Imm8RexEffect (BitVec.ofNat 64 0x101a1a) (.sib 4 (some 15) 0 (.d8 16)) 128 t).components =
            [.mem (stackPtr t + (.reg 15 : Operand 64).read t + 16) 1, .rip] by
          x86_norm [BitVec.shiftLeft_zero, stackPtr]; rfl)
        rw [hs, hp]
        simpa [relocated, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
          using hc 0x1a13 26 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a20 (by decide +kernel)
    md5_run_then (lea_r64_effect_step (BitVec.ofNat 64 0x101a20) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a24 (by decide +kernel)
    md5_run_then (add_r64_imm8_effect_step (BitVec.ofNat 64 0x101a24) 0x48 0xc7 17
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 17 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a28 (by decide +kernel)
    md5_run_then (xor_r32_r32_effect_step (BitVec.ofNat 64 0x101a28) 0xf6 (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 21 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a2a (by decide +kernel)
    md5_run_then (mov_r64_r64_effect_step (BitVec.ofNat 64 0x101a2a) 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x101a13)) 23 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a2d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [paddingEffect]
    · x86_norm [paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
      simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
    · intro i; cases i <;> x86_norm [paddingEffect]
    · x86_norm [paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
      simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Streams.Slices
