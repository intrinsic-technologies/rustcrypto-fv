import P256.Proofs.Verifying.Wrapper.LocalMemory
import P256.Proofs.Verifying.Wrapper.KeyArguments
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.MessageStore

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1031b7
  writable : CrossPageStore.Writable s ((Operand.reg 4#5 : Operand 64).read s+152) 16
  apart : RangeApart ((Operand.reg 4#5 : Operand 64).read s+152) 16 0x1031b7#64 16

def bytes : List UInt8 :=
  [72, 137, 140, 36, 152, 0, 0, 0, 72, 137, 132, 36, 160, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1031c7
    writes := [⟨(.mem ((Operand.reg 4#5 : Operand 64).read s+152) : Operand 64),s.regValue .rcx⟩,
      ⟨(.mem ((Operand.reg 4#5 : Operand 64).read s+160) : Operand 64),s.regValue .rax⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1031b7 bytes) (Effect.post effect) := by
  advance_begin (CrossPageStore.mov_m64_r64_effect_step_any 0x1031b7 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip,?_,?_⟩
    · change CrossPageStore.Writable s ((Operand.reg 4#5 : Operand 64).read s+152) 8
      simpa using h.writable.add 0 (by decide : 0+8 ≤ 16)
    · change RangeApart ((Operand.reg 4#5 : Operand 64).read s+152) 8 0x1031b7#64 8
      simpa using (P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 0
        (by decide : 0+8 ≤ 16)).sub 0 8 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa using P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 0
      (by decide : 0+8 ≤ 16)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x31bf (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1031bf 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1031b7 bytes 8 8
  case mid =>
    intro s t h hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm
      simpa only [BitVec.add_assoc,BitVec.reduceAdd] using h.writable.add 8 (by decide)
    · x86_norm
      simpa only [BitVec.add_assoc,BitVec.reduceAdd] using
        (P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 8
          (by decide : 8+8 ≤ 16)).sub 8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.add_assoc,BitVec.reduceAdd] using
        P256.Proofs.Common.Instructions.RangeApart.add_left h.apart 8 (by decide : 8+8 ≤ 16)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x31c7 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Wrapper.MessageStore
