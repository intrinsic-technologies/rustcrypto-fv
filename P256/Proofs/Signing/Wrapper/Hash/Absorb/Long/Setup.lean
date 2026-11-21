import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.ReadWrite.Rmw

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Setup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x102820
  writable : MemWritable s (stackPtr s + 272) 8
  apart : RangeApart (stackPtr s + 272) 8 0x102820 11

def bytes : List UInt8 :=
  [0x48,0x89,0xac,0x24,0x10,0x01,0x00,0x00,0x48,0x89,0xea]

def effect (s : RamState) : Effect :=
  { rip := 0x10282b
    writes := [⟨(.mem (stackPtr s + 272) : Operand 64), s.regValue .rbp⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rbp⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102820 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2820 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x102820 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_r64_effect_step 0x102820 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.writable, h.apart.sub 0 8 (by decide)⟩
  case av =>
    intro s h
    exact Effect.avoids_of_mem (by x86_norm [Effect.components, Component.isMem]) h.apart rfl
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x2828 (by decide))
  advance_then (mov_r64_r64_effect_step 0x102828 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102820 bytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x282b (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Setup
