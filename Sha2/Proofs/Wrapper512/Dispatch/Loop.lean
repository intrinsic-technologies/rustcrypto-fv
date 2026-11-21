import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.EffectCompose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.Variant
import Sha2.Proofs.Wrapper512.ResetLayout
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Dispatch.Loop

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes : List UInt8 := [0x49,0x89,0xf7,0x45,0x31,0xf6,0xeb,0x3c]

def effect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc 0x11d
    writes := [⟨(.reg 15 : Operand 64), (.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xd9) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xd9) bytes
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc 0xd9) (codeRange (v.pc 0xd9) bytes)
      (Effect.post (effect v)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect (v.pc 0xd9) 15 6) from
    mov_r64_r64_effect_step (v.pc 0xd9) 0x49 0xf7
      (by simp [RexWPrefix]) rfl)
  case «next» => exact fun _ _ => boundary_ne_program outside (by
    have h := Variant.pc_inProgram v (by cases v <;> decide : 0xdc < 1024)
    simpa [movR64R64Effect, Variant.pc_add] using h)
  advance_then (show StepEffect _ _ (xorR32R32Effect (v.pc 0xdc) 3 14 14) from
    xor_r32_r32_rex_effect_step (v.pc 0xdc) 0x45 0xf6
      (by simp [RexNoWPrefix]) rfl)
  case sub =>
    have hpc : v.pc 0xd9 + BitVec.ofNat 64 3 = v.pc 0xdc := by
      simpa only [show 0xd9 + 3 = 0xdc by decide] using Variant.pc_add v 0xd9 3
    rw [← hpc]
    exact codeRange_slice_subset (v.pc 0xd9) bytes 3 3
  case mid =>
    intro s t _ hH _
    have hpc : v.pc 0xd9 + BitVec.ofNat 64 3 = v.pc 0xdc := by
      simpa only [show 0xd9 + 3 = 0xdc by decide] using Variant.pc_add v 0xd9 3
    refine ⟨hH.rip.trans hpc, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (by
      have h := Variant.pc_inProgram v (by cases v <;> decide : 0xdf < 1024)
      simpa [xorR32R32Effect, Variant.pc_add] using h)
  advance_then (show StepEffect _ _ (fun _ => nopEffect (v.pc 0x11d) 0) from
    have htarget : branchTarget (v.pc 0xdf) 2 ((0x3c : BitVec 8).signExtend 64) =
        v.pc 0x11d := by
      cases v <;> decide
    have hjump : (fun _ : RamState => jmpEffect (v.pc 0xdf) 2 ((0x3c : BitVec 8).signExtend 64)) =
        (fun _ => nopEffect (v.pc 0x11d) 0) := by
      funext s
      simp only [jmpEffect, nopEffect]
      rw [htarget]
      simp
    hjump ▸ jmp_rel8_effect_step (v.pc 0xdf) 0x3c (by
      have h := congrArg BitVec.toNat htarget
      rw [h]
      cases v <;> decide))
  case sub =>
    have hpc : v.pc 0xd9 + BitVec.ofNat 64 6 = v.pc 0xdf := by
      simpa only [show 0xd9 + 6 = 0xdf by decide] using Variant.pc_add v 0xd9 6
    rw [← hpc]
    exact codeRange_slice_subset (v.pc 0xd9) bytes 6 2
  case mid =>
    intro s t _ hH _
    have hpc : v.pc 0xdc + BitVec.ofNat 64 3 = v.pc 0xdf := by
      simpa only [show 0xdc + 3 = 0xdf by decide] using Variant.pc_add v 0xdc 3
    refine ⟨hH.rip.trans hpc, Effect.Avoids.of_noMem
      (by simp [nopEffect, Effect.components, Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (by
      have h := Variant.pc_inProgram v (by cases v <;> decide : 0x11d < 1024)
      simpa [nopEffect] using h)
  advance_finish [effect, nopEffect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.add_zero]

def resetFirstBytes : List UInt8 := [0x45, 0x31, 0xff, 0xeb, 0x2d]

def resetFirstPC (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 ((ResetLayout.reset v).textOffset + 0xf2)

def resetFirstEffect (v : Variant) (_s : RamState) : Effect :=
  { rip := resetFirstPC v + 50
    writes := [⟨(.reg 15 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem resetFirst_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (resetFirstPC v) resetFirstBytes) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    ((ResetLayout.reset v).textOffset + 0xf2) resetFirstBytes
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem reset_first_run [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = resetFirstPC v)
      (codeRange (resetFirstPC v) resetFirstBytes) (Effect.post (resetFirstEffect v)) := by
  have inside : BlockInProgram (resetFirstPC v) 50 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide
  unfold resetFirstEffect
  generalize hpc : resetFirstPC v = p at *
  have target : InProgram (p + 50) := inside 50 (by decide)
  have low : (branchTarget (p + 3) 2 ((45 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (show StepEffect _ _ (xorR32R32Effect (p) 3 15 15) from
    xor_r32_r32_rex_effect_step (p) 0x45 0xff
      (by simp [RexNoWPrefix]) rfl)
    next (boundary_ne_program outside (inside 3 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 3) 45 low)
    next (boundary_ne_program outside target)
  advance_finish [ BitVec.xor_self, BitVec.setWidth_zero]

def resetNextBytes : List UInt8 := [0x45, 0x31, 0xff, 0x48, 0x89, 0xe3, 0xeb, 0x2b]

def resetNextPC (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 ((ResetLayout.reset v).textOffset + 0x29e)

def resetNextEffect (v : Variant) (_s : RamState) : Effect :=
  { rip := resetNextPC v + 51
    writes := [⟨(.reg 15 : Operand 64), 0⟩,
      ⟨(.reg 3 : Operand 64), (.reg 4 : Operand 64).read _s⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem resetNext_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (resetNextPC v) resetNextBytes) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    ((ResetLayout.reset v).textOffset + 0x29e) resetNextBytes
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem reset_next_run [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = resetNextPC v)
      (codeRange (resetNextPC v) resetNextBytes) (Effect.post (resetNextEffect v)) := by
  have inside : BlockInProgram (resetNextPC v) 51 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide
  unfold resetNextEffect
  generalize hpc : resetNextPC v = p at *
  have target : InProgram (p + 51) := inside 51 (by decide)
  have low : (branchTarget (p + 6) 2 ((43 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (show StepEffect _ _ (xorR32R32Effect (p) 3 15 15) from
    xor_r32_r32_rex_effect_step (p) 0x45 0xff
      (by simp [RexNoWPrefix]) rfl)
    next (boundary_ne_program outside (inside 3 (by decide)))
  advance_reloc_then (show StepEffect _ _ (movR64R64Effect (p + 3) 3 4) from
    mov_r64_r64_effect_step (p + 3) 0x48 0xe3 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 6 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 6) 43 low)
    next (boundary_ne_program outside target)
  advance_finish [BitVec.xor_self, BitVec.setWidth_zero]

def resetLastOffset (v : Variant) (finalize : Bool := false) : Nat :=
  match finalize, v with
  | false, .sha384 => 0x4cfe
  | false, .sha512 => 0xa9ac
  | false, .sha512_224 => 0x6baf
  | false, .sha512_256 => 0x8a10
  | true, .sha384 => 0x43c1
  | true, .sha512 => 0xa02f
  | true, .sha512_224 => 0x62b2
  | true, .sha512_256 => 0x8113

def resetLastDisplacement (v : Variant) (finalize : Bool := false) : BitVec 32 :=
  match finalize, v with
  | false, .sha384 => 0x9058
  | false, .sha512 => 0x33aa
  | false, .sha512_224 => 0x71a7
  | false, .sha512_256 => 0x5346
  | true, .sha384 => 0x9995
  | true, .sha512 => 0x3d27
  | true, .sha512_224 => 0x7aa4
  | true, .sha512_256 => 0x5c43

def resetLastJump (v : Variant) (finalize : Bool := false) : BitVec 8 :=
  match finalize, v with
  | false, .sha384 => 0x23
  | false, .sha512 => 0x25
  | false, .sha512_224 => 0x22
  | false, .sha512_256 => 0x21
  | true, .sha384 => 0x27
  | true, .sha512 => 0x29
  | true, .sha512_224 => 0x27
  | true, .sha512_256 => 0x26

def resetLastPC (v : Variant) (finalize : Bool := false) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (resetLastOffset v finalize)

def resetLastIndex (finalize : Bool) : BitVec 5 := if finalize then 14 else 15

def resetLastPointer (v : Variant) (finalize : Bool) : BitVec 4 :=
  if finalize && (v == .sha512_224 || v == .sha512_256) then 12 else 3

def resetLastBytes (v : Variant) (finalize : Bool := false) : List UInt8 :=
  [0x45, 0x31, if finalize then 0xf6 else 0xff] ++
    encodeLeaR64M (resetLastPointer v finalize) (.rip (resetLastDisplacement v finalize)) ++
    [0xeb] ++ immBytes 8 (resetLastJump v finalize)

def resetLastEffect (v : Variant) (_s : RamState) (finalize : Bool := false) : Effect :=
  { rip := resetLastPC v finalize + 12 + (resetLastJump v finalize).signExtend 64
    writes := [⟨(.reg (resetLastIndex finalize) : Operand 64), 0⟩,
      ⟨(.reg ((resetLastPointer v finalize).setWidth 5) : Operand 64), resetLastPC v finalize + 10 + (resetLastDisplacement v finalize).signExtend 64⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem resetLast_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) (finalize : Bool := false) :
    CodeIn (codeRange (resetLastPC v finalize) (resetLastBytes v finalize)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (resetLastOffset v finalize) (resetLastBytes v finalize)
  · cases finalize <;> cases v <;> decide
  · cases finalize <;> cases v <;> decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem reset_last_run [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (finalize : Bool := false) :
    AdvanceTriple boundary (fun s => s.RIP = resetLastPC v finalize)
      (codeRange (resetLastPC v finalize) (resetLastBytes v finalize))
      (Effect.post (fun s => resetLastEffect v s finalize)) := by
  have inside : BlockInProgram (resetLastPC v finalize) 64 := by
    apply blockInProgram_of_textOffset
    cases finalize <;> cases v <;> decide
  have target : InProgram (resetLastPC v finalize + 12 + (resetLastJump v finalize).signExtend 64) := by
    have eq : (resetLastJump v finalize).signExtend 64 =
        BitVec.ofNat 64 (resetLastJump v finalize).toNat := by
      cases finalize <;> cases v <;> decide
    rw [eq]
    have h := inside (12 + (resetLastJump v finalize).toNat) (by cases finalize <;> cases v <;> decide)
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using h
  have low : (branchTarget (resetLastPC v finalize + 10) 2
      ((resetLastJump v finalize).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  unfold resetLastEffect resetLastBytes
  generalize hp : resetLastPC v finalize = p at *
  generalize hd : resetLastDisplacement v finalize = displacement at *
  generalize hj : resetLastJump v finalize = jump at *
  have zero : StepEffect (fun s => s.RIP = p)
      (codeRange p [0x45, 0x31, if finalize then 0xf6 else 0xff])
      (xorR32R32Effect p 3 (resetLastIndex finalize) (resetLastIndex finalize)) := by
    cases finalize
    · exact xor_r32_r32_rex_effect_step p 0x45 0xff (by simp [RexNoWPrefix]) rfl
    · exact xor_r32_r32_rex_effect_step p 0x45 0xf6 (by simp [RexNoWPrefix]) rfl
  have address := Sha2.Proofs.Common.SHA256.Absorb.Blocks.address_step
    (p + 3) (resetLastPointer v finalize) (.rip displacement) (by simp [AddrMode.Valid])
  cases finalize <;> cases v <;> (
    advance_reloc_begin zero next (boundary_ne_program outside (inside 3 (by decide)))
    try (case sub => exact codeRange_mem_of_take (by simp))
    advance_reloc_then address
      next (boundary_ne_program outside (inside 10 (by decide)))
    try (case sub => exact codeRange_mem_of_drop 3 (by
      simp [encodeLeaR64M, AddrMode.modrm, AddrMode.mod, AddrMode.rm,
        AddrMode.tail, immBytes_length]))
    advance_reloc_then (jmp_rel8_effect_step (p + 10) jump low)
      next (boundary_ne_program outside (by simpa [BitVec.add_assoc] using target))
    try (case sub => exact codeRange_mem_of_drop 10 (by
      simp [encodeLeaR64M, AddrMode.tail, immBytes]))
    advance_finish [resetLastIndex, resetLastPointer, BitVec.xor_self, BitVec.setWidth_zero]
  )

def finalizeFirstCopiesCount (v : Variant) : Bool := v == .sha384 || v == .sha512

def finalizeFirstSetupBytes (copyCount : Bool) : List UInt8 :=
  (if copyCount then [0x49, 0x89, 0xf4] else []) ++ [0x45, 0x31, 0xf6]

def finalizeFirstSetupPC (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 ((ResetLayout.finalizeIntoReset v).textOffset +
    (ResetLayout.finalizeIntoResetInitializationEnds v)[0]!)

def finalizeFirstSetupEffect (p : BitVec 64) (copyCount : Bool) (s : RamState) : Effect :=
  { rip := p + (if copyCount then 6 else 3)
    writes := (if copyCount then [⟨(.reg 12 : Operand 64), (.reg 6 : Operand 64).read s⟩]
      else []) ++ [⟨(.reg 14 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem finalizeFirstSetup_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (finalizeFirstSetupPC v)
      (finalizeFirstSetupBytes (finalizeFirstCopiesCount v))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    ((ResetLayout.finalizeIntoReset v).textOffset +
      (ResetLayout.finalizeIntoResetInitializationEnds v)[0]!)
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem finalize_first_setup [Bindings] (p : BitVec 64) (copyCount : Bool)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p 6) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (finalizeFirstSetupBytes copyCount))
      (Effect.post (finalizeFirstSetupEffect p copyCount)) := by
  cases copyCount with
  | false =>
    advance_reloc_begin (show StepEffect _ _ (xorR32R32Effect p 3 14 14) from
      xor_r32_r32_rex_effect_step p 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
      next (boundary_ne_program outside (inside 3 (by decide)))
    advance_finish [finalizeFirstSetupEffect, BitVec.xor_self, BitVec.setWidth_zero]
  | true =>
    advance_reloc_begin (show StepEffect _ _ (movR64R64Effect p 12 6) from
      mov_r64_r64_effect_step p 0x49 0xf4 (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 3 (by decide)))
    advance_reloc_then (show StepEffect _ _ (xorR32R32Effect (p + 3) 3 14 14) from
      xor_r32_r32_rex_effect_step (p + 3) 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
      next (boundary_ne_program outside (inside 6 (by decide)))
    advance_finish [finalizeFirstSetupEffect, BitVec.xor_self, BitVec.setWidth_zero]

def finalizeFirstEmptyBytes (copyCount : Bool) : List UInt8 :=
  [0x45, 0x31, if copyCount then 0xff else 0xe4, 0x31, 0xc0, 0xe9, 0x3d, 0x01, 0, 0]

def finalizeFirstEmptyPC (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 ((ResetLayout.finalizeIntoReset v).textOffset + 0xe5)

def finalizeFirstEmptyEffect (p : BitVec 64) (copyCount : Bool) (_s : RamState) : Effect :=
  { rip := p + 327
    writes := [⟨(.reg (if copyCount then 15 else 12) : Operand 64), 0⟩,
      ⟨(.reg 0 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem finalizeFirstEmpty_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (finalizeFirstEmptyPC v)
      (finalizeFirstEmptyBytes (finalizeFirstCopiesCount v))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    ((ResetLayout.finalizeIntoReset v).textOffset + 0xe5)
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem finalize_first_empty [Bindings] (p : BitVec 64) (copyCount : Bool)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p 327) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (finalizeFirstEmptyBytes copyCount))
      (Effect.post (finalizeFirstEmptyEffect p copyCount)) := by
  have low : (branchTarget (p + 5) 5 ((317 : BitVec 32).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := inside 327 (by decide)
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  have zero : StepEffect (fun s => s.RIP = p)
      (codeRange p [0x45, 0x31, if copyCount then 0xff else 0xe4])
      (xorR32R32Effect p 3 (if copyCount then 15 else 12) (if copyCount then 15 else 12)) := by
    cases copyCount
    · exact xor_r32_r32_rex_effect_step p 0x45 0xe4 (by simp [RexNoWPrefix]) rfl
    · exact xor_r32_r32_rex_effect_step p 0x45 0xff (by simp [RexNoWPrefix]) rfl
  cases copyCount <;> (
    advance_reloc_begin zero next (boundary_ne_program outside (inside 3 (by decide)))
    try (case sub => exact codeRange_mem_of_take (by simp [finalizeFirstEmptyBytes]))
    advance_reloc_then (show StepEffect _ _ (xorR32R32Effect (p + 3) 2 0 0) from
      xor_r32_r32_effect_step (p + 3) 0xc0 rfl)
      next (boundary_ne_program outside (inside 5 (by decide)))
    try (case sub => exact codeRange_mem_of_drop 3 (by simp [finalizeFirstEmptyBytes]))
    advance_reloc_then (jmp_rel32_effect_step (p + 5) 317 low)
      next (boundary_ne_program outside (inside 327 (by decide)))
    advance_finish [finalizeFirstEmptyEffect, BitVec.xor_self, BitVec.setWidth_zero]
  )

def traitCloneBytes (second : Bool) : List UInt8 :=
  [0x45, 0x31, 0xff] ++ encodeLeaR64M 3 (.sib 4 none 0 (.d8 32)) ++
    encodeLeaR64M (if second then 14 else 12) (.sib 4 none 0 (.d32 256))

def traitCloneEffect (p : BitVec 64) (second : Bool) (s : RamState) : Effect :=
  { rip := p + 16
    writes := [⟨(.reg 15 : Operand 64), 0⟩,
      ⟨(.reg 3 : Operand 64), rspOf s + 32⟩,
      ⟨(.reg (if second then 14 else 12) : Operand 64), rspOf s + 256⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem trait_clone_setup [Bindings] (p : BitVec 64) (second : Bool)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p 16) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (traitCloneBytes second))
      (Effect.post (traitCloneEffect p second)) := by
  have address := Sha2.Proofs.Common.SHA256.Absorb.Blocks.address_step (p + 8)
    (if second then 14 else 12) (.sib 4 none 0 (.d32 256)) (by decide)
  cases second <;> (
    advance_reloc_begin (show StepEffect _ _ (xorR32R32Effect p 3 15 15) from
      xor_r32_r32_rex_effect_step p 0x45 0xff (by simp [RexNoWPrefix]) rfl)
      next (boundary_ne_program outside (inside 3 (by decide)))
    advance_reloc_then (Sha2.Proofs.Common.SHA256.Absorb.Blocks.address_step
      (p + 3) 3 (.sib 4 none 0 (.d8 32)) (by decide))
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_reloc_then address next (boundary_ne_program outside (inside 16 (by decide)))
    advance_finish [traitCloneEffect, BitVec.xor_self, BitVec.setWidth_zero]
  )

def memcpyJumpBytes (pointer : BitVec 4) (displacement : BitVec 32) (jump : BitVec 8) : List UInt8 :=
  encodeLeaR64M pointer (.rip displacement) ++ [0xeb] ++ immBytes 8 jump

def memcpyJumpEffect (p : BitVec 64) (pointer : BitVec 4) (displacement : BitVec 32)
    (jump : BitVec 8) (_s : RamState) : Effect :=
  { rip := p + 9 + jump.signExtend 64
    writes := [⟨(.reg (pointer.setWidth 5) : Operand 64), p + 7 + displacement.signExtend 64⟩] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem memcpy_jump [Bindings] (p : BitVec 64) (pointer : BitVec 4)
    (displacement : BitVec 32) (jump : BitVec 8) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 9)
    (target : InProgram (p + 9 + jump.signExtend 64)) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (memcpyJumpBytes pointer displacement jump))
      (Effect.post (memcpyJumpEffect p pointer displacement jump)) := by
  have low : (branchTarget (p + 7) 2 (jump.signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (Sha2.Proofs.Common.SHA256.Absorb.Blocks.address_step
    p pointer (.rip displacement) (by simp [AddrMode.Valid]))
    next (boundary_ne_program outside (inside 7 (by decide)))
  try (case sub => exact codeRange_mem_of_take (by
    simp [memcpyJumpBytes, encodeLeaR64M, AddrMode.tail, immBytes_length]))
  advance_reloc_then (jmp_rel8_effect_step (p + 7) jump low)
    next (boundary_ne_program outside (by simpa [BitVec.add_assoc] using target))
  try (case sub => exact codeRange_mem_of_drop 7 (by
    simp [memcpyJumpBytes, encodeLeaR64M, AddrMode.tail, immBytes]))
  advance_finish [memcpyJumpEffect]

def traitLoopOffset (v : Variant) (second : Bool) : Nat :=
  (ResetLayout.traitFinalizeIntoReset v).textOffset +
    (if second then (ResetLayout.traitFinalizeIntoResetInitializationEnds v)[1]! + 12 else 0xec)

def traitLoopPC (v : Variant) (second : Bool) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (traitLoopOffset v second)

def traitMemcpyDisplacement (v : Variant) (second : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (0xdd60 - (traitLoopOffset v second + 23))

def traitLoopJump (v : Variant) (second : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (((ResetLayout.traitFinalizeIntoReset v).traversals.map ResetLayout.Traversal.head)[if second then 1 else 0]! -
    (if second then (ResetLayout.traitFinalizeIntoResetInitializationEnds v)[1]! + 12 else 0xec) - 25)

theorem traitClone_code {v : Variant} {second : Bool} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (traitLoopPC v second) (traitCloneBytes second)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (traitLoopOffset v second)
  · cases second <;> cases v <;> decide
  · cases second <;> cases v <;> decide +kernel

theorem traitMemcpy_code {v : Variant} {second : Bool} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (traitLoopPC v second + 16)
      (memcpyJumpBytes (if second then 5 else 13) (traitMemcpyDisplacement v second)
        (traitLoopJump v second))) s := by
  have h := programText_slice (programLoaded_codeIn loaded) (traitLoopOffset v second + 16)
    (memcpyJumpBytes (if second then 5 else 13) (traitMemcpyDisplacement v second) (traitLoopJump v second))
    (by cases second <;> cases v <;> decide) (by cases second <;> cases v <;> decide +kernel)
  simpa [traitLoopPC, BitVec.ofNat_add, BitVec.add_assoc] using h

def traitSaveOffset (v : Variant) (output : Bool) : Nat :=
  (ResetLayout.traitFinalizeIntoReset v).textOffset + if output then 0xe4 else 0xd6

def traitSavePC (v : Variant) (output : Bool) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (traitSaveOffset v output)

def traitSaveSource (v : Variant) (output : Bool) : BitVec 4 :=
  if output then (if v = .sha512 then 13 else 5) else 6

def traitSaveSlot (output : Bool) : Disp := if output then .d32 240 else .d8 8

def traitSaveBytes (v : Variant) (output : Bool) : List UInt8 :=
  encodeMovM64R64 (traitSaveSource v output) (.sib 4 none 0 (traitSaveSlot output))

theorem traitSave_code {v : Variant} {output : Bool} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (traitSavePC v output) (traitSaveBytes v output)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (traitSaveOffset v output)
  · cases output <;> cases v <;> decide
  · cases output <;> cases v <;> decide +kernel


def resetTransitionHead : Form → Bool
  | .finalizeIntoReset _ | .traitFinalizeIntoReset _ => false
  | _ => true

def resetTransitionBase (v : Variant) : Form → Nat
  | .finalizeIntoReset _ => 14
  | .traitFinalizeIntoReset _ => if v = .sha512 then 5 else 3
  | _ => 0

def resetTransitionRegister (form : Form) : Nat := if resetTransitionHead form then 1 else 0

def resetTransitionHashOffset : Form → Nat
  | .finalizeIntoReset _ => 144
  | .traitFinalizeIntoReset _ => 384
  | _ => 128

def resetTransitionLength (v : Variant) (form : Form) : Nat :=
  (if resetTransitionHead form then 148 else 143) + if resetTransitionBase v form = 5 then 1 else 0

def resetTransitionBytes (v : Variant) (form : Form := .reset 1) : List UInt8 :=
  (if resetTransitionHead form then ([0x48,0x8d,0x84,0x24,0x80,0,0,0] : List UInt8) else []) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[6]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),48] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[4]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),32] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[2]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),16] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[0]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  (if resetTransitionBase v form = 5 then ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + 5),0] : List UInt8) else [UInt8.ofNat (8 * resetTransitionRegister form + resetTransitionBase v form % 8)]) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[7]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),56] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[5]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),40] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[3]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),24] : List UInt8) ++
  ([0x48, UInt8.ofNat (0xb8 + resetTransitionRegister form)] : List UInt8) ++ immBytes 64 v.initialHash[1]!.toBitVec ++
  ([UInt8.ofNat (0x48 + resetTransitionBase v form / 8),0x89] : List UInt8) ++
  ([UInt8.ofNat (0x40 + 8 * resetTransitionRegister form + resetTransitionBase v form % 8),8] : List UInt8) ++
  ([0x48,0xc7,0x84,0x24] : List UInt8) ++ immBytes 32 (BitVec.ofNat 32 (resetTransitionHashOffset form + 64)) ++ [0,0,0,0] ++
  ([0x48,0xc7,0x84,0x24] : List UInt8) ++ immBytes 32 (BitVec.ofNat 32 (resetTransitionHashOffset form + 72)) ++ [0,0,0,0] ++
  (if resetTransitionHead form then [0xc6,0x44,0x24,127,0] else ([0xc6,0x84,0x24] : List UInt8) ++ immBytes 32 (BitVec.ofNat 32 (resetTransitionHashOffset form - 1)) ++ [0])

structure ResetTransitionPre (p : BitVec 64) (s : RamState) (form : Form := .reset 1)
    (v : Variant := .sha384) : Prop where
  rip : s.RIP = p
  writeTail : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form - 1)) 1
  apartTail : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form - 1)) 1 p 148
  write0 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 0)) 8
  apart0 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 0)) 8 p 148
  write8 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 8)) 8
  apart8 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 8)) 8 p 148
  write16 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 16)) 8
  apart16 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 16)) 8 p 148
  write24 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 24)) 8
  apart24 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 24)) 8 p 148
  write32 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 32)) 8
  apart32 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 32)) 8 p 148
  write40 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 40)) 8
  apart40 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 40)) 8 p 148
  write48 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 48)) 8
  apart48 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 48)) 8 p 148
  write56 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 56)) 8
  apart56 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 56)) 8 p 148
  write64 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 64)) 8
  apart64 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 64)) 8 p 148
  write72 : MemWritable s (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 72)) 8
  apart72 : RangeApart (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 72)) 8 p 148
  base : resetTransitionHead form = false →
    (.reg (BitVec.ofNat 5 (resetTransitionBase v form)) : Operand 64).read s =
      rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form)

def resetTransitionEffect (v : Variant) (p : BitVec 64) (s : RamState) (form : Form := .reset 1) : Effect :=
  { rip := p + BitVec.ofNat 64 (resetTransitionLength v form)
    writes := [⟨(.reg (BitVec.ofNat 5 (resetTransitionBase v form)) : Operand 64), rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form)⟩] ++
      [⟨(.reg (BitVec.ofNat 5 (resetTransitionRegister form)) : Operand 64), v.initialHash[1]!.toBitVec⟩] ++
    [
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 56)) : Operand 64), v.initialHash[7]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 48)) : Operand 64), v.initialHash[6]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 40)) : Operand 64), v.initialHash[5]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 32)) : Operand 64), v.initialHash[4]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 24)) : Operand 64), v.initialHash[3]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 16)) : Operand 64), v.initialHash[2]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 8)) : Operand 64), v.initialHash[1]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 0)) : Operand 64), v.initialHash[0]!.toBitVec⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 72)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form + 64)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form - 1)) : Operand 8), 0⟩] }

def resetTransitionStart (v : Variant) (p : BitVec 64) (s : RamState) (form : Form) : Effect :=
  { rip := p
    writes := [⟨(.reg (BitVec.ofNat 5 (resetTransitionBase v form)) : Operand 64),
      rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form)⟩] }

theorem reset_transition_start [Bindings] (v : Variant) (p : BitVec 64)
    (boundary : ReturnBoundary) (form : Form) (head : resetTransitionHead form = false) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s form v)
      (codeRange p (resetTransitionBytes v form))
      (Effect.post (fun s => resetTransitionStart v p s form)) := by
  intro s ready loaded pre
  refine ⟨0, s, rfl, ready, loaded, pre.rip, ?_, trivial, AgreesExcept.refl _ _⟩
  exact pre.base head

attribute [local x86_compose] resetTransitionStart resetTransitionHead resetTransitionBase resetTransitionRegister resetTransitionHashOffset resetTransitionLength

macro "sha512_restore_after_first " v:term "," p:term "," base:term "," reg:term "," rex:term "," hash:term "," start:term "," extra:term "," zero:term "," tail:term "," length:term "," outside:term "," inside:term : tactic => `(tactic| (
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 10)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 48)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 14) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 14)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[4]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 24) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 24)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 32)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 28) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 28)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[2]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 38) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 38)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 16)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 42) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 42)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[0]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 52) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 52)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) ($zero)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 55 + $extra) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 55 + $extra)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[7]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 65 + $extra) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 65 + $extra)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 56)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 69 + $extra) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 69 + $extra)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[5]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 79 + $extra) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 79 + $extra)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 40)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 83 + $extra) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 83 + $extra)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[3]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 93 + $extra) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 93 + $extra)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 24)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 97 + $extra) (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step ($p + ($start + 97 + $extra)) 0x48 (UInt8.ofNat (0xb8 + $reg)) (by simp [RexWPrefix]) (by decide) ($v).initialHash[1]!.toBitVec)
    next (boundary_ne_program $outside ($inside ($start + 107 + $extra) (by decide)))
  advance_reloc_then (mov_m64_r64_effect_step ($p + ($start + 107 + $extra)) $rex (by simp [RexWPrefix]) (BitVec.ofNat 3 $reg) (.base (BitVec.ofNat 4 $base) (.d8 8)) (by decide) rfl (by decide))
    next (boundary_ne_program $outside ($inside ($start + 111 + $extra) (by decide)))
  advance_reloc_then (mov_m64_imm32_effect_step ($p + ($start + 111 + $extra)) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 ($hash + 64)))) (by decide) rfl rfl 0)
    next (boundary_ne_program $outside ($inside ($start + 123 + $extra) (by decide)))
  advance_reloc_then (mov_m64_imm32_effect_step ($p + ($start + 123 + $extra)) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 ($hash + 72)))) (by decide) rfl rfl 0)
    next (boundary_ne_program $outside ($inside ($start + 135 + $extra) (by decide)))
  advance_reloc_then (mov_m8_imm8_effect_step ($p + ($start + 135 + $extra)) (.sib 4 none 0 $tail) (by decide) rfl rfl 0)
    next (boundary_ne_program $outside ($inside $length (by decide)))
  advance_finish [resetTransitionEffect]
  all_goals (try dsimp only [resetTransitionHead, resetTransitionRegister, resetTransitionBase, resetTransitionHashOffset])
  all_goals (try (cases ($v) <;> x86_sub))

))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 900000 in
private theorem reset_transition_reset [Bindings] (v : Variant) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.reset 1) v)
      (codeRange p (resetTransitionBytes v (.reset 1)))
      (Effect.post (fun s => resetTransitionEffect v p s (.reset 1))) := by
  unfold resetTransitionBytes
  advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step (p + 8) 0x48 0xb9 (by simp [RexWPrefix]) (by decide) v.initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 18 (by decide)))
  sha512_restore_after_first v, p, 0, 1, 0x48, 128, 8, 0, (.none), (.d8 127), 148, outside, inside
  all_goals (cases v <;> x86_sub)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 900000 in
private theorem reset_transition_finalize [Bindings] (v : Variant) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.finalizeIntoReset true) v)
      (codeRange p (resetTransitionBytes v (.finalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionEffect v p s (.finalizeIntoReset true))) := by
  refine (show (AdvanceTriple boundary (fun s => ResetTransitionPre p s (.finalizeIntoReset true) v)
      (codeRange p (resetTransitionBytes v (.finalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionStart v p s (.finalizeIntoReset true)))) → _ from ?_)
    (reset_transition_start v p boundary (.finalizeIntoReset true) rfl)
  unfold resetTransitionBytes
  advance_reloc_then (mov_r64_imm64_effect_step p 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (v).initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 10 (by decide)))
  sha512_restore_after_first v, p, 14, 0, 0x49, 144, 0, 0, (.none), (.d32 143), 143, outside, inside
  all_goals (cases v <;> x86_sub)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
private theorem reset_transition_trait_sha384 [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) .sha384)
      (codeRange p (resetTransitionBytes .sha384 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionEffect .sha384 p s (.traitFinalizeIntoReset true))) := by
  refine (show (AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) Variant.sha384)
      (codeRange p (resetTransitionBytes Variant.sha384 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionStart Variant.sha384 p s (.traitFinalizeIntoReset true)))) → _ from ?_)
    (reset_transition_start Variant.sha384 p boundary (.traitFinalizeIntoReset true) rfl)
  unfold resetTransitionBytes
  advance_reloc_then (mov_r64_imm64_effect_step p 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (Variant.sha384).initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 10 (by decide)))
  sha512_restore_after_first Variant.sha384, p, 3, 0, 0x48, 384, 0, 0, (.none), (.d32 383), 143, outside, inside
  all_goals x86_sub

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
private theorem reset_transition_trait_sha512 [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) .sha512)
      (codeRange p (resetTransitionBytes .sha512 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionEffect .sha512 p s (.traitFinalizeIntoReset true))) := by
  refine (show (AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) Variant.sha512)
      (codeRange p (resetTransitionBytes Variant.sha512 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionStart Variant.sha512 p s (.traitFinalizeIntoReset true)))) → _ from ?_)
    (reset_transition_start Variant.sha512 p boundary (.traitFinalizeIntoReset true) rfl)
  unfold resetTransitionBytes
  advance_reloc_then (mov_r64_imm64_effect_step p 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (Variant.sha512).initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 10 (by decide)))
  sha512_restore_after_first Variant.sha512, p, 5, 0, 0x48, 384, 0, 1, (.d8 0), (.d32 383), 144, outside, inside
  all_goals x86_sub

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
private theorem reset_transition_trait_sha512_224 [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) .sha512_224)
      (codeRange p (resetTransitionBytes .sha512_224 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionEffect .sha512_224 p s (.traitFinalizeIntoReset true))) := by
  refine (show (AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) Variant.sha512_224)
      (codeRange p (resetTransitionBytes Variant.sha512_224 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionStart Variant.sha512_224 p s (.traitFinalizeIntoReset true)))) → _ from ?_)
    (reset_transition_start Variant.sha512_224 p boundary (.traitFinalizeIntoReset true) rfl)
  unfold resetTransitionBytes
  advance_reloc_then (mov_r64_imm64_effect_step p 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (Variant.sha512_224).initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 10 (by decide)))
  sha512_restore_after_first Variant.sha512_224, p, 3, 0, 0x48, 384, 0, 0, (.none), (.d32 383), 143, outside, inside
  all_goals x86_sub

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
private theorem reset_transition_trait_sha512_256 [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) .sha512_256)
      (codeRange p (resetTransitionBytes .sha512_256 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionEffect .sha512_256 p s (.traitFinalizeIntoReset true))) := by
  refine (show (AdvanceTriple boundary (fun s => ResetTransitionPre p s (.traitFinalizeIntoReset true) Variant.sha512_256)
      (codeRange p (resetTransitionBytes Variant.sha512_256 (.traitFinalizeIntoReset true)))
      (Effect.post (fun s => resetTransitionStart Variant.sha512_256 p s (.traitFinalizeIntoReset true)))) → _ from ?_)
    (reset_transition_start Variant.sha512_256 p boundary (.traitFinalizeIntoReset true) rfl)
  unfold resetTransitionBytes
  advance_reloc_then (mov_r64_imm64_effect_step p 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (Variant.sha512_256).initialHash[6]!.toBitVec)
    next (boundary_ne_program outside (inside 10 (by decide)))
  sha512_restore_after_first Variant.sha512_256, p, 3, 0, 0x48, 384, 0, 0, (.none), (.d32 383), 143, outside, inside
  all_goals x86_sub


def resetTransitionOffset (v : Variant) : Form → Nat
  | .finalizeIntoReset _ => v.outputEndOffset (.finalizeIntoReset false)
  | .traitFinalizeIntoReset _ => v.outputEndOffset (.traitFinalizeIntoReset false)
  | _ => 0x20a

set_option maxRecDepth 2048 in
theorem resetTransition_code {v : Variant} {s : RamState} (loaded : ProgramLoaded s)
    (form : Form := .reset 1) (phase : form = .reset 1 ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true := by decide) :
    CodeIn (codeRange (v.pc (resetTransitionOffset v form) form) (resetTransitionBytes v form)) s := by
  have h := programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + resetTransitionOffset v form) (resetTransitionBytes v form)
    (by rcases phase with rfl | rfl | rfl <;> cases v <;> decide)
    (by rcases phase with rfl | rfl | rfl <;> cases v <;> decide +kernel)
  exact h


theorem reset_transition [Bindings] (v : Variant) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 148)
    (form : Form := .reset 1) (phase : form = .reset 1 ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true := by decide) :
    AdvanceTriple boundary (fun s => ResetTransitionPre p s form v) (codeRange p (resetTransitionBytes v form))
      (Effect.post (fun s => resetTransitionEffect v p s form)) := by
  rcases phase with rfl | rfl | rfl
  · exact reset_transition_reset v p boundary outside inside
  · exact reset_transition_finalize v p boundary outside inside
  · cases v with
    | sha384 => exact reset_transition_trait_sha384 p boundary outside inside
    | sha512 => exact reset_transition_trait_sha512 p boundary outside inside
    | sha512_224 => exact reset_transition_trait_sha512_224 p boundary outside inside
    | sha512_256 => exact reset_transition_trait_sha512_256 p boundary outside inside

end Sha2.Proofs.Wrapper512.Dispatch.Loop
