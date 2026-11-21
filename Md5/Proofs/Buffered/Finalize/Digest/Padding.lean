import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Buffered.Finalize.Store8
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.Finalize.Digest.Padding

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

structure RunPre (s : RamState) : Prop extends Storage .digest s where
  rip : s.RIP = 0x100107
  position : ((.reg 12 : Operand 64).read s).toNat < 64

def effect (s : RamState) : Effect :=
  let pos := (.reg 12 : Operand 64).read s
  { rip := 0x10011a
    writes := [⟨(.mem (stackPtr s + pos + 24) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + 25⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

attribute [x86_compose] effect

@[x86_local] theorem effect_local : Effect.Local effect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · have hsp : stackPtr t = stackPtr t' := h.read (.reg 4 : Operand 64) trivial
    simp only [effect, hsp, h.read_reg]
  · cases i <;> rfl
  · simp [effect, Write.Full, Operand.Full]

def bytes : List UInt8 :=
  [0x42, 0xc6, 0x44, 0x24, 0x18, 0x80, 0x4a, 0x8d, 0x3c, 0x24,
    0x48, 0x83, 0xc7, 0x19, 0x31, 0xf6, 0x4c, 0x89, 0xf2]

theorem marker_writable {s : RamState} (hs : Storage .digest s)
    (hp : ((.reg 12 : Operand 64).read s).toNat < 64) :
    Memory.MemWritable s (stackPtr s + (.reg 12 : Operand 64).read s + 24) 1 := by
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
    hs.stackWritable (((.reg 12 : Operand 64).read s).toNat + 24) 1 (by simp only [Kind.stackBytes]; omega)

theorem marker_apart {s : RamState} (hs : Storage .digest s)
    (hp : ((.reg 12 : Operand 64).read s).toNat < 64) (offset len : Nat)
    (hc : offset + len ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + (.reg 12 : Operand 64).read s + 24) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hs.stackApart
      (offset := ((.reg 12 : Operand 64).read s).toNat + 24) (len := 1)
      (codeOffset := offset) (codeLen := len) (by simp only [Kind.stackBytes]; omega) hc

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary RunPre (codeRange 0x100107 bytes) effect := by
  unfold bytes
  md5_run_begin (Finalize.mov_m8_imm8_rex_effect_step 0x100107 0x42
    (by unfold RexPrefix; decide) (.sib 4 (some 12) 0 (.d8 24))
    (by decide) (by decide) (by decide) 128)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm [BitVec.shiftLeft_zero]
      simpa [stackPtr, Operand.read, BitVec.add_assoc] using marker_writable h.toStorage h.position
    · x86_norm [BitVec.shiftLeft_zero]
      simpa [stackPtr, Operand.read, BitVec.add_assoc, Extracted.textAddress] using marker_apart h.toStorage h.position 0x107 6 (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip (show
      (Finalize.movM8Imm8RexEffect 0x100107 (.sib 4 (some 12) 0 (.d8 24)) 128 s).components =
        [.mem (stackPtr s + (.reg 12 : Operand 64).read s + 24) 1, .rip] by x86_norm [BitVec.shiftLeft_zero, stackPtr]; rfl)
    exact marker_apart h.toStorage h.position 0x107 19 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x10d (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x10010d 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100107) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x111 (by decide +kernel)
  md5_run_then (add_r64_imm8_effect_step 0x100111 0x48 0xc7 25
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100107) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x115 (by decide +kernel)
  md5_run_then (xor_r32_r32_effect_step 0x100115 0xf6 (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100107) 14 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x117 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100117 0x4c 0xf2
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100107) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x11a (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr, BitVec.shiftLeft_zero]
    simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr, BitVec.shiftLeft_zero]
    rfl

end Md5.Proofs.Buffered.Finalize.Digest.Padding
