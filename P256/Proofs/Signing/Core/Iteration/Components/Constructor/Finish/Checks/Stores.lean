import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StoresPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ off ∈ ([24,16,8,0] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([24,16,8,0] : List (BitVec 64)), ∀ k len : Nat,
    k + len ≤ 35 → RangeApart (stackPtr s + off) 8 (p + BitVec.ofNat 64 k) len

def storesBytes : List UInt8 :=
  [72,199,68,36,24,0,0,0,0,72,199,68,36,16,0,0,0,0,
   72,199,68,36,8,0,0,0,0,72,199,4,36,0,0,0,0]

def storesEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 35
    writes := [⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), 0⟩] }

set_option maxHeartbeats 800000 in
theorem stores_correct [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (safe : ∀ k ∈ ([9#64,18#64,27#64,35#64] : List (BitVec 64)), p + k ≠ boundary.rip) :
    AdvanceTriple boundary (StoresPre p) (codeRange p storesBytes)
      (Effect.post (storesEffect p)) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any p 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · exact h.writable 24 (by simp)
    · x86_norm [stackPtr, storesBytes]
      simpa only [stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.codeApart 24 (by simp) 0 9 (by decide)
  case next =>
    intro s h
    exact safe 9 (by simp)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr, storesBytes]
    simpa only [stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.codeApart 24 (by simp) 0 35 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any (p + 9) 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 9 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr, storesBytes]
      simpa only [stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.codeApart 16 (by simp) 0 35 (by decide)
    · x86_norm
      exact safe 18 (by simp)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any (p + 18) 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 18 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr, storesBytes]
      simpa only [stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.codeApart 8 (by simp) 0 35 (by decide)
    · x86_norm
      exact safe 27 (by simp)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any (p + 27) 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 0 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 0 (by simp) 27 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr, storesBytes]
      simpa only [stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.codeApart 0 (by simp) 0 35 (by decide)
    · x86_norm
      exact safe 35 (by simp)
  advance_finish [storesEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
