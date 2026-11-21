import X86Proofs.Program.Entry
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry.Zero

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x116333
  writable : ∀ slot ∈ ([56,48,40,32,24,16,8,0] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 slot) 8
  codeApart : ∀ slot ∈ ([56,48,40,32,24,16,8,0] : List Nat),
    ∀ offset len : Nat, 0x116333 ≤ offset → offset + len ≤ 0x11637a →
    RangeApart (rspOf s + BitVec.ofNat 64 slot) 8 (BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x38,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x30,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x28,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x20,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x18,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x10,0,0,0,0,
   0x48,0xc7,0x44,0x24,0x08,0,0,0,0,
   0x48,0xc7,0x04,0x24,0,0,0,0]

def effect (s : RamState) : Effect :=
  { rip := 0x11637a
    writes := [
      ⟨(.mem (rspOf s + 56) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s) : Operand 64), 0⟩] }

theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x116333 ≤ ip → ip ≤ 0x11637a →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x116333 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x116333 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 56 (by simp), h.codeApart 56 (by simp) 0x116333 9 (by decide) (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 56 (by simp) 0x116333 71 (by decide) (by decide)
  case next => exact fun _ _ => outside 0x11633c (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x11633c 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x11633c 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x116345 (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x116345 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x116345 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x11634e (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x11634e 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x11634e 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x116357 (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x116357 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 36 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x116357 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x116360 (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x116360 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 45 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x116360 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x116369 (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x116369 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 54 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x116369 9 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x116372 (by decide) (by decide)
  advance_then (mov_m64_imm32_effect_step 0x116372 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x116333 bytes 63 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x116372 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x116333 71 (by decide) (by decide)
    · exact outside 0x11637a (by decide) (by decide)
  advance_finish [effect, BitVec.add_zero]

end Hkdf.Proofs.Key.Entry.Zero
