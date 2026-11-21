import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook

def source (s : RamState) : BitVec 64 := (Operand.reg 1 : Operand 64).read s

def destination (s : RamState) : BitVec 64 := (Operand.reg 12 : Operand 64).read s

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a643
  r15 : (Operand.reg 15#5 : Operand 64).read s = 0#64
  readable : ∀ offset ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s (source s + offset) 8
  writable : ∀ offset ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemWritable s (destination s + offset) 8
  codeApart : ∀ offset ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ codeOffset codeLen : Nat, codeOffset + codeLen ≤ 118431 →
    RangeApart (destination s + offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen
  sourceApart : ∀ first ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ second ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    RangeApart (destination s + first) 8 (source s + second) 8

def bytes : List UInt8 := [0x48, 0x8b, 0x41, 0x18, 0x4b, 0x89, 0x44, 0x3c, 0x18, 0x48, 0x8b, 0x41, 0x10, 0x4b, 0x89, 0x44, 0x3c, 0x10, 0x48, 0x8b, 0x1, 0x48, 0x8b, 0x49, 0x8, 0x4b, 0x89, 0x4c, 0x3c, 0x8, 0x4b, 0x89, 0x4, 0x3c]

def effect (s : RamState) : Effect :=
  { rip := 0x10a665
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (source s) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (source s + 8) 64⟩,
      ⟨(.mem (destination s) : Operand 64), memLoad s.external (source s) 64⟩,
      ⟨(.mem (destination s + 8) : Operand 64), memLoad s.external (source s + 8) 64⟩,
      ⟨(.mem (destination s + 16) : Operand 64), memLoad s.external (source s + 16) 64⟩,
      ⟨(.mem (destination s + 24) : Operand 64), memLoad s.external (source s + 24) 64⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a643 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa643 bytes (by decide) (by decide +kernel)

theorem Pre.source_read {s : RamState} (pre : Pre s) (memory : Ram) (value : BitVec 64)
    {first second : BitVec 64} (hf : first ∈ ([0, 8, 16, 24] : List (BitVec 64)))
    (hs : second ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
    memLoad (memStore memory (destination s + first) value) (source s + second) 64 =
      memLoad memory (source s + second) 64 := by
  apply memLoad_memStore_rangeApart
  exact pre.sourceApart first hf second hs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a643 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10a643 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 24 (by simp)⟩
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0xa647 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a647 0x4b (by simp [RexWPrefix]) 0
    (.sib 12 (some 15) 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0xa647 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0xa643 34 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa64c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a64c 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa [source, rspOf, BitVec.add_zero] using hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa650 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a650 0x4b (by simp [RexWPrefix]) 0
    (.sib 12 (some 15) 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0xa650 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0xa643 34 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa655 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a655 0x48 (by simp [RexWPrefix]) 0
    (.base 1 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa [source, rspOf, BitVec.add_zero] using hP.readable 0 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa658 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a658 0x48 (by simp [RexWPrefix]) 1
    (.base 1 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 21 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa [source, rspOf, BitVec.add_zero] using hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa65c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a65c 0x4b (by simp [RexWPrefix]) 1
    (.sib 12 (some 15) 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0xa65c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0xa643 34 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa661 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a661 0x4b (by simp [RexWPrefix]) 0
    (.sib 12 (some 15) 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a643 bytes 30 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0xa661 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [hP.r15, BitVec.shiftLeft_zero]
      simpa only [BitVec.ofNat_eq_ofNat, destination, rspOf, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0xa643 34 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa665 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have read := @Pre.source_read s hP
  simp only [source, destination, BitVec.ofNat_eq_ofNat] at read
  have readZero (memory : Ram) (value : BitVec 64) {first : BitVec 64}
      (hf : first ∈ ([0, 8, 16, 24] : List (BitVec 64))) :=
    Pre.source_read hP memory value hf (second := 0) (by simp)
  simp only [source, destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at readZero
  apply hH.weaken
  · x86_norm [effect, read, readZero, source, destination, rspOf, hP.r15, BitVec.shiftLeft_zero, operand_write_reg_external, operand_write_mem_external, BitVec.add_zero]
  · x86_norm [effect, read, readZero, source, destination, rspOf, hP.r15, BitVec.shiftLeft_zero, operand_write_reg_external, operand_write_mem_external, BitVec.add_zero]
  · intro i; cases i <;> x86_norm [effect, read, readZero, source, destination, rspOf, hP.r15, BitVec.shiftLeft_zero, operand_write_reg_external, operand_write_mem_external, BitVec.add_zero]
  · x86_norm [effect, read, readZero, source, destination, rspOf, hP.r15, BitVec.shiftLeft_zero, operand_write_reg_external, operand_write_mem_external, BitVec.add_zero]

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Buffer
