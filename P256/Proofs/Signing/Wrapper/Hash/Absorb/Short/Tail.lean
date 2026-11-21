import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Tail

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x102793
  writable : MemWritable s (stackPtr s + 239) 1
  codeApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + 239) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 := [0x40,0x88,0xac,0x24,0xef,0,0,0,0xe9,0xac,0,0,0]

def effect (s : RamState) : Effect :=
  { rip := 0x10284c
    writes := [⟨(.mem (stackPtr s + 239) : Operand 8), (s.regValue .rbp).setWidth 8⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102793 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2793 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x102793 bytes) (Effect.post effect) := by
  advance_begin (mov_m8_r8_effect_step 0x102793 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.codeApart 0x2793 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 0x2793 13 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x279b (by decide))
  advance_then (jmp_rel32_effect_step 0x10279b 0xac (by decide))
  case sub => exact codeRange_slice_subset 0x102793 bytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x284c (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Tail
