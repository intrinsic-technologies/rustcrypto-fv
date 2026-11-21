import Hkdf.Proofs.Common.SHA256.Entry.LoadWords
import Hkdf.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Nop.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.LegacyLoad
open Hkdf.Proofs.Common.Instructions.CrossPageStore (Writable)

structure StatePointerPre (s : RamState) : Prop where
  rip : s.RIP = 0x109604
  writable : Writable s (stackPtr s + 192) 8
  readable : MemReadable s (s.regValue .rdi + 28) 4
  apart : RangeApart (stackPtr s + 192) 8 0x109604 12
  hashApart : RangeApart (stackPtr s + 192) 8 (s.regValue .rdi + 28) 4

def statePointerBytes : List UInt8 :=
  [0x48,0x89,0xbc,0x24,0xc0,0,0,0,0x8b,0x4f,0x1c,0x90]

def statePointerEffect (s : RamState) : Effect :=
  { rip := 0x109610
    writes := [⟨(Operand.mem (stackPtr s + 192) : Operand 64), s.regValue .rdi⟩,
      ⟨(Operand.reg 1 : Operand 64), (memLoad s.external (s.regValue .rdi + 28) 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem state_pointer_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StatePointerPre (codeRange 0x109604 statePointerBytes)
      (Effect.post statePointerEffect) := by
  advance_begin Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x109604 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_, ?_⟩
    · x86_norm; exact hp.writable
    · x86_norm
      intro i hi j hj
      exact hp.apart i hi j (by omega)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.apart
  case next => intro s hp; exact boundary_ne_program outside (inProgram_of_textOffset 0x960c (by decide))
  advance_then mov_r32_m32_legacy_effect_step 0x10960c 1 (.base 7 (.d8 28)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x109604 statePointerBytes 8 3
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers, movR32M32LegacyEffect_components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x960f (by decide))⟩
    x86_norm
    exact hp.readable
  advance_then nop_effect_step 0x10960f
  case sub => exact codeRange_slice_subset 0x109604 statePointerBytes 11 1
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), nopEffect_avoids _ _ _,
      boundary_ne_program outside (inProgram_of_textOffset 0x9610 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  have unchanged := Hkdf.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
    s.external (stackPtr s + 192) (s.regValue .rdi + 28) (s.regValue .rdi) 32 hp.hashApart
  apply hh.weaken
  · x86_norm [nopEffect, statePointerEffect]
  · x86_norm [nopEffect, statePointerEffect]
    exact ⟨rfl, congrArg (BitVec.setWidth 64) unchanged.symm⟩
  · intro i; cases i <;> x86_norm [nopEffect, statePointerEffect]
  · x86_norm [nopEffect, statePointerEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end Hkdf.Proofs.Common.SHA256
