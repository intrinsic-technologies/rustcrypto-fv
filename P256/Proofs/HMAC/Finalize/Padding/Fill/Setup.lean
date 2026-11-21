import P256.Proofs.HMAC.Finalize.Padding.Fill.Call
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import P256.Proofs.Common.Instructions.StoreByte
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.EffectCompose.Advance
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding.FillSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Common.Instructions

attribute [local x86_compose] P256.Proofs.Common.Instructions.movM8Imm8RexEffect BitVec.shiftLeft_zero BitVec.xor_self BitVec.setWidth_zero
attribute [local x86_local] P256.Proofs.Common.Instructions.movM8Imm8RexEffect_local

def posReg (outer : Bool) : BitVec 5 := if outer then 12 else 13
def countReg (outer : Bool) : BitVec 5 := if outer then 13 else 5
def hashReg (outer : Bool) : BitVec 5 := if outer then 14 else 15
def zeroReg (outer : Bool) : BitVec 5 := if outer then 15 else 12

def position (s : RamState) : BitVec 64 :=
  (memLoad s.external (rspOf s + 135) 8).setWidth 64

structure Pre (outer : Bool) (s : RamState) : Prop where
  rip : s.RIP = paddingStart outer
  tailLength : MemReadable s (rspOf s + 135) 1
  blocks : MemReadable s (rspOf s + 168) 8
  writable : MemWritable s (rspOf s + position s + 72) 1
  codeApart : RangeApart (rspOf s + position s + 72) 1 (paddingStart outer) 51

def bytes (outer : Bool) : List UInt8 :=
  if outer then [0x4c,0x8d,0xb4,0x24,0x88,0x0,0x0,0x0,0x44,0xf,0xb6,0xa4,0x24,0x87,0x0,0x0,0x0,0x4c,0x8b,0xac,0x24,0xa8,0x0,0x0,0x0,0x4d,0x89,0xe7,0x49,0x83,0xf7,0x3f,0x42,0xc6,0x44,0x24,0x48,0x80,0x4a,0x8d,0x3c,0x24,0x48,0x83,0xc7,0x49,0x31,0xf6,0x4c,0x89,0xfa] else [0x4c,0x8d,0xbc,0x24,0x88,0x0,0x0,0x0,0x44,0xf,0xb6,0xac,0x24,0x87,0x0,0x0,0x0,0x48,0x8b,0xac,0x24,0xa8,0x0,0x0,0x0,0x4d,0x89,0xec,0x49,0x83,0xf4,0x3f,0x42,0xc6,0x44,0x2c,0x48,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x83,0xc7,0x49,0x31,0xf6,0x4c,0x89,0xe2]

def effect (outer : Bool) (s : RamState) : Effect :=
  { rip := fillCall outer
    writes := [⟨(.reg (hashReg outer) : Operand 64), rspOf s + 136⟩,
      ⟨(.reg (posReg outer) : Operand 64), position s⟩,
      ⟨(.reg (countReg outer) : Operand 64), memLoad s.external (rspOf s + 168) 64⟩,
      ⟨(.reg (zeroReg outer) : Operand 64), position s ^^^ 63⟩,
      ⟨(.mem (rspOf s + position s + 72) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + position s + 73⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), position s ^^^ 63⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code (outer : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (paddingStart outer) (bytes outer)) s := by
  cases outer
  · exact programText_slice (programLoaded_codeIn loaded) 0xfb7 _ (by decide) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x1255 _ (by decide) (by decide +kernel)

theorem run [Bindings] (outer : Bool) (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre outer) (codeRange (paddingStart outer) (bytes outer))
      (Effect.post (effect outer)) := by
  cases outer
  · advance_begin (lea_r64_effect_step 0x100fb7 0x4c (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
    case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xfbf (by decide))
    advance_then (show StepEffect _ _ (movzxR32M8Effect 0x100fbf 9 13 (.sib 4 none 0 (.d32 135))) from
        movzx_r_m8_rex_effect_step 0x100fbf 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
          (fun _ => rfl) 5 (.sib 4 none 0 (.d32 135)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 8 9
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
      · x86_norm
        exact hp.tailLength
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc8 (by decide))
    advance_then (mov_r64_m64_effect_step 0x100fc8 0x48 (by simp [RexWPrefix]) 5
        (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 17 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
      · x86_norm
        exact hp.blocks
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfd0 (by decide))
    advance_then (mov_r64_r64_effect_step 0x100fd0 0x4d 0xec (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 25 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfd3 (by decide))
    advance_then (StepEffect.forgetFlags (h := xor_r64_imm8_effect_step 0x100fd3 0x49 0xf4 63
        (by simp [RexWPrefix]) rfl rfl))
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 28 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfd7 (by decide))
    advance_then (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x100fd7 0x42 (by simp [RexNoWPrefix])
        (.sib 4 (some 13) 0 (.d8 72)) (by decide) rfl rfl 128)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 32 6
    case mid =>
      intro s t hp hh ho
      refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        simpa [position, rspOf, Operand.read, BitVec.add_assoc] using hp.writable
      · x86_norm
        intro i hi j hj
        simpa [position, paddingStart, BitVec.ofNat_add, ← BitVec.add_assoc, rspOf, Operand.read]
          using hp.codeApart i hi (32+j) (by omega)
      · apply Effect.Local.avoids (by x86_local) (ho true)
        apply Effect.avoids_codeRange
        x86_norm
        simpa [position, rspOf, Operand.read, BitVec.add_assoc, bytes] using hp.codeApart
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfdd (by decide))
    advance_then (lea_r64_effect_step 0x100fdd 0x4a (by simp [RexWPrefix]) 7
        (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 38 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfe1 (by decide))
    advance_then (StepEffect.forgetFlags (h := add_r64_imm8_effect_step 0x100fe1 0x48 0xc7 73
        (by simp [RexWPrefix]) rfl rfl))
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 42 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfe5 (by decide))
    advance_then (StepEffect.forgetFlags (h := xor_r32_r32_effect_step 0x100fe5 0xf6 rfl))
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 46 2
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfe7 (by decide))
    advance_then (mov_r64_r64_effect_step 0x100fe7 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x100fb7 (bytes false) 48 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xfea (by decide))
    advance_finish [effect, fillCall, position, posReg, countReg, hashReg, zeroReg, BitVec.add_assoc, BitVec.reduceAdd, show modrmReg 246 = modrmRm 246 by decide +kernel]
  · advance_begin (lea_r64_effect_step 0x101255 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
    case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x125d (by decide))
    advance_then (show StepEffect _ _ (movzxR32M8Effect 0x10125d 9 12 (.sib 4 none 0 (.d32 135))) from
        movzx_r_m8_rex_effect_step 0x10125d 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
          (fun _ => rfl) 4 (.sib 4 none 0 (.d32 135)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 8 9
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
      · x86_norm
        exact hp.tailLength
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1266 (by decide))
    advance_then (mov_r64_m64_effect_step 0x101266 0x4c (by simp [RexWPrefix]) 5
        (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 17 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
      · x86_norm
        exact hp.blocks
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x126e (by decide))
    advance_then (mov_r64_r64_effect_step 0x10126e 0x4d 0xe7 (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 25 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1271 (by decide))
    advance_then (StepEffect.forgetFlags (h := xor_r64_imm8_effect_step 0x101271 0x49 0xf7 63
        (by simp [RexWPrefix]) rfl rfl))
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 28 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1275 (by decide))
    advance_then (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x101275 0x42 (by simp [RexNoWPrefix])
        (.sib 4 (some 12) 0 (.d8 72)) (by decide) rfl rfl 128)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 32 6
    case mid =>
      intro s t hp hh ho
      refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        simpa [position, rspOf, Operand.read, BitVec.add_assoc] using hp.writable
      · x86_norm
        intro i hi j hj
        simpa [position, paddingStart, BitVec.ofNat_add, ← BitVec.add_assoc, rspOf, Operand.read]
          using hp.codeApart i hi (32+j) (by omega)
      · apply Effect.Local.avoids (by x86_local) (ho true)
        apply Effect.avoids_codeRange
        x86_norm
        simpa [position, rspOf, Operand.read, BitVec.add_assoc, bytes] using hp.codeApart
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x127b (by decide))
    advance_then (lea_r64_effect_step 0x10127b 0x4a (by simp [RexWPrefix]) 7
        (.sib 4 (some 12) 0 .none) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 38 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x127f (by decide))
    advance_then (StepEffect.forgetFlags (h := add_r64_imm8_effect_step 0x10127f 0x48 0xc7 73
        (by simp [RexWPrefix]) rfl rfl))
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 42 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1283 (by decide))
    advance_then (StepEffect.forgetFlags (h := xor_r32_r32_effect_step 0x101283 0xf6 rfl))
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 46 2
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1285 (by decide))
    advance_then (mov_r64_r64_effect_step 0x101285 0x4c 0xfa (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x101255 (bytes true) 48 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1288 (by decide))
    advance_finish [effect, fillCall, position, posReg, countReg, hashReg, zeroReg, BitVec.add_assoc, BitVec.reduceAdd, show modrmReg 246 = modrmRm 246 by decide +kernel]

end P256.Proofs.HMAC.Finalize.Padding.FillSetup
