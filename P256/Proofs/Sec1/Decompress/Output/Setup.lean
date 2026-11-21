import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

attribute [local x86_compose] movM8Imm8Effect

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x11008f
  writable : MemWritable s ((Operand.reg 4 : Operand 64).read s + 64) 1
  readable : MemReadable s ((Operand.reg 4 : Operand 64).read s + 184) 8
  codeApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + 64) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def setupBytes : List UInt8 :=
  [0xc6,0x44,0x24,0x40,0,0x48,0x89,0xe6,0xb9,9,0,0,0,
   0x48,0x8b,0x9c,0x24,0xb8,0,0,0,0x48,0x89,0xdf]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x1100a7
    writes := [
      ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 3 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 184) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 184) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x11008f setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x11008f (.sib 4 none 0 (.d8 64))
    (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable, hP.codeApart 0x1008f 5 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 0x1008f 24 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x10094 (by decide))
  advance_then (mov_r64_r64_effect_step 0x110094 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11008f setupBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10097 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x110097 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x11008f setupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1009c (by decide))
  advance_then (mov_r64_m64_effect_step 0x11009c 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11008f setupBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x100a4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1100a4 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11008f setupBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x100a7 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (m : Ram) : memLoad (memStore m ((Operand.reg 4 : Operand 64).read s + 64#64) (0#8))
      ((Operand.reg 4 : Operand 64).read s + 184#64) 64 =
      memLoad m ((Operand.reg 4 : Operand 64).read s + 184#64) 64 := by
    apply memLoad_congr
    intro j hj
    simp only [memByte, PhysicalMemory.read]
    rw [memStore_getElem?_of_ne]
    intro i hi
    exact RangeApart.offsets ((Operand.reg 4 : Operand 64).read s)
      (a := 64) (b := 184) (len := 1) (count := 8)
      (by decide) (by decide) (.inl (by decide)) i hi j hj
  apply hH.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, operand_write_reg_external, hread]
    all_goals first | rfl | exact Or.inr rfl
  · intro i; cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]

end P256.Proofs.Sec1.Decompress.Output
