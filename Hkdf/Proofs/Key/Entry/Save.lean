import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.Entry

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry.Save

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x116320
  writable : ∀ offset ∈ ([8,16,24,32,40] : List Nat),
    MemWritable s (rspOf s - BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([8,16,24,32,40] : List Nat),
    ∀ ip len : Nat, 0x116320 ≤ ip → ip + len ≤ 0x116333 →
    RangeApart (rspOf s - BitVec.ofNat 64 offset) 8 (BitVec.ofNat 64 ip) len

def bytes : List UInt8 :=
  [0x41,0x57,0x41,0x56,0x41,0x55,0x41,0x54,0x53,
   0x48,0x81,0xec,0x50,0x01,0,0,0x48,0x89,0xfb]

def effect (s : RamState) : Effect :=
  { rip := 0x116333
    writes := [
      ⟨(.reg 4 : Operand 64), rspOf s - 376⟩,
      ⟨(.mem (rspOf s - 8) : Operand 64), s.regValue .r15⟩,
      ⟨(.mem (rspOf s - 16) : Operand 64), s.regValue .r14⟩,
      ⟨(.mem (rspOf s - 24) : Operand 64), s.regValue .r13⟩,
      ⟨(.mem (rspOf s - 32) : Operand 64), s.regValue .r12⟩,
      ⟨(.mem (rspOf s - 40) : Operand 64), s.regValue .rbx⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩]
    flags := some (.ofStatusFlags (subSpec (rspOf s - 40) 336).2) }

theorem pushAddr_eq_rspOf (s : RamState) : pushAddr s = rspOf s - 8 := rfl

theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x116320 ≤ ip → ip ≤ 0x116333 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x116320 bytes) (Effect.post effect) := by
  advance_begin (push_r64_rex_effect_step 0x116320 0x41 0x57
    (by simp [RexPrefix]) (by decide +kernel))
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 8 (by simp), h.codeApart 8 (by simp) 0x116320 2 (by decide) (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
    exact h.codeApart 8 (by simp) 0x116320 19 (by decide) (by decide)
  case next => exact fun _ _ => outside 0x116322 (by decide) (by decide)
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (push_r64_rex_effect_step 0x116322 0x41 0x56 (by simp [RexPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116320 bytes 2 2
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.writable 16 (by simp)
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 16 (by simp) 0x116322 2 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 16 (by simp) 0x116320 19 (by decide) (by decide)
    · exact outside 0x116324 (by decide) (by decide)
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (push_r64_rex_effect_step 0x116324 0x41 0x55 (by simp [RexPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116320 bytes 4 2
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.writable 24 (by simp)
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 24 (by simp) 0x116324 2 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 24 (by simp) 0x116320 19 (by decide) (by decide)
    · exact outside 0x116326 (by decide) (by decide)
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (push_r64_rex_effect_step 0x116326 0x41 0x54 (by simp [RexPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116320 bytes 6 2
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.writable 32 (by simp)
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 32 (by simp) 0x116326 2 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 32 (by simp) 0x116320 19 (by decide) (by decide)
    · exact outside 0x116328 (by decide) (by decide)
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (push_r64_effect_step 0x116328 0x53 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116320 bytes 8 1
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.writable 40 (by simp)
    · x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 40 (by simp) 0x116328 1 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
      exact hP.codeApart 40 (by simp) 0x116320 19 (by decide) (by decide)
    · exact outside 0x116329 (by decide) (by decide)
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (sub_r64_imm32_effect_step 0x116329 0x48 0xec 336
    (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x116320 bytes 9 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]), by x86_avoid,
      outside 0x116330 (by decide) (by decide)⟩
  x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]
  advance_then (mov_r64_r64_effect_step 0x116330 0x48 0xfb
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x116320 bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [pushAddr_eq_rspOf, BitVec.sub_sub]), by x86_avoid,
      outside 0x116333 (by decide) (by decide)⟩
  apply Hkdf.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [effect, pushAddr_eq_rspOf, BitVec.sub_sub, BitVec.sub_eq_add_neg]
  · x86_norm [effect, pushAddr_eq_rspOf, BitVec.sub_sub, BitVec.sub_eq_add_neg]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [effect, pushAddr_eq_rspOf, BitVec.sub_sub, BitVec.sub_eq_add_neg]
  · x86_norm [effect, pushAddr_eq_rspOf, BitVec.sub_sub, BitVec.sub_eq_add_neg]

end Hkdf.Proofs.Key.Entry.Save
