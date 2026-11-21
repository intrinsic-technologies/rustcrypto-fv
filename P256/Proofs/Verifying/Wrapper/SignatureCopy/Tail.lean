import P256.Proofs.Verifying.Wrapper.SignatureCopy.Word8
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10318d
  first : MemReadable s ((Operand.reg 4#5 : Operand 64).read s+80) 8
  second : MemReadable s ((Operand.reg 4#5 : Operand 64).read s+88) 8
  writable : CrossPageStore.Writable s ((Operand.reg 4#5 : Operand 64).read s) 16
  apart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 16 0x10318d#64 19

def bytes : List UInt8 :=
  [72, 139, 68, 36, 80, 72, 139, 76, 36, 88, 72, 137, 76, 36, 8, 72, 137, 4, 36]

def effect (s : RamState) : Effect :=
  { rip := 0x1031a0
    writes := [⟨(.reg 0 : Operand 64),memLoad s.external ((Operand.reg 4#5 : Operand 64).read s+80) 64⟩,
      ⟨(.reg 1 : Operand 64),memLoad s.external ((Operand.reg 4#5 : Operand 64).read s+88) 64⟩,
      ⟨(.mem ((Operand.reg 4#5 : Operand 64).read s+8) : Operand 64),
        memLoad s.external ((Operand.reg 4#5 : Operand 64).read s+88) 64⟩,
      ⟨(.mem ((Operand.reg 4#5 : Operand 64).read s+0) : Operand 64),
        memLoad s.external ((Operand.reg 4#5 : Operand 64).read s+80) 64⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10318d bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10318d 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.first⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x3192 (by decide))
  advance_then (mov_r64_m64_effect_step 0x103192 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10318d bytes 5 5
  case mid =>
    intro s t h hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x3197 (by decide))⟩
    x86_norm
    exact h.second
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x103197 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10318d bytes 10 5
  case mid =>
    intro s t h hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm
      exact h.writable.add 8 (by decide)
    · x86_norm
      exact (P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 8 (by decide : 8+8 ≤ 16)).sub 10 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 8 (by decide : 8+8 ≤ 16)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x319c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10319c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10318d bytes 15 4
  case mid =>
    intro s t h hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm
      simpa only [BitVec.add_zero,BitVec.reduceAdd] using h.writable.add 0 (by decide : 0+8 ≤ 16)
    · x86_norm
      simpa only [BitVec.add_zero,BitVec.reduceAdd] using
        (P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 0 (by decide : 0+8 ≤ 16)).sub 15 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.add_zero,BitVec.reduceAdd] using P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 0 (by decide : 0+8 ≤ 16)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x31a0 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Wrapper.SignatureCopy.Tail
