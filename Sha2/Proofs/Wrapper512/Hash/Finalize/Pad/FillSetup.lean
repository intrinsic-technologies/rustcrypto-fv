import Sha2.Proofs.Wrapper.Hash.Padding.StoreByte
import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Common.EffectCompose.Advance
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Fill
import Sha2.Proofs.Wrapper512.Variant
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
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
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.FillSetup

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Wrapper.Hash.Padding

attribute [local x86_compose] Sha2.Proofs.Wrapper.Hash.Padding.movM8Imm8RexEffect movM8Imm8Effect incR64Effect addR64Imm8Effect BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

@[local x86_local] theorem byteStore_local (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (Sha2.Proofs.Wrapper.Hash.Padding.movM8Imm8RexEffect p am imm) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Sha2.Proofs.Wrapper.Hash.Padding.movM8Imm8RexEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [Sha2.Proofs.Wrapper.Hash.Padding.movM8Imm8RexEffect, storeEffect, Write.Full, Operand.Full]

def tailIndex (encoding : Fin 9) : BitVec 5 :=
  match encoding.val with
  | 0 => 13
  | 1 => 5
  | 2 => 5
  | 3 => 12
  | 4 => 13
  | 5 => 13
  | 6 => 13
  | 7 => 12
  | _ => 13

def displacement (encoding : Fin 9) : Nat :=
  match encoding.val with
  | 0 => 32
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 240
  | 6 => 256
  | 7 => 256
  | _ => 32

def paddingIndex (encoding : Fin 9) : BitVec 5 :=
  match encoding.val with
  | 0 => 3
  | 1 => 15
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 14
  | 6 => 14
  | 7 => 3
  | _ => 14

def bytesAt (encoding : Fin 9) : List UInt8 :=
  match encoding.val with
  | 0 => [0x42,0xc6,0x44,0x2c,0x20,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x83,0xc7,0x21,0x31,0xf6,0x48,0x89,0xda]
  | 1 => [0xc6,0x4,0x2c,0x80,0x48,0x8d,0x3c,0x2c,0x48,0xff,0xc7,0x31,0xf6,0x4c,0x89,0xfa]
  | 2 => [0xc6,0x4,0x2c,0x80,0x48,0x8d,0x3c,0x2c,0x48,0xff,0xc7,0x31,0xf6,0x48,0x89,0xda]
  | 3 => [0x42,0xc6,0x4,0x24,0x80,0x4a,0x8d,0x3c,0x24,0x48,0xff,0xc7,0x31,0xf6,0x48,0x89,0xda]
  | 4 => [0x42,0xc6,0x44,0x2c,0x10,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x83,0xc7,0x11,0x31,0xf6,0x48,0x89,0xda]
  | 5 => [0x42,0xc6,0x84,0x2c,0xf0,0x0,0x0,0x0,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x81,0xc7,0xf1,0x0,0x0,0x0,0x31,0xf6,0x4c,0x89,0xf2]
  | 6 => [0x42,0xc6,0x84,0x2c,0x0,0x1,0x0,0x0,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x81,0xc7,0x1,0x1,0x0,0x0,0x31,0xf6,0x4c,0x89,0xf2]
  | 7 => [0x42,0xc6,0x84,0x24,0x0,0x1,0x0,0x0,0x80,0x4a,0x8d,0x3c,0x24,0x48,0x81,0xc7,0x1,0x1,0x0,0x0,0x31,0xf6,0x48,0x89,0xda]
  | _ => [0x42,0xc6,0x44,0x2c,0x20,0x80,0x4a,0x8d,0x3c,0x2c,0x48,0x83,0xc7,0x21,0x31,0xf6,0x4c,0x89,0xf2]

structure PreAt (p : BitVec 64) (encoding : Fin 9) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (rspOf s + (Operand.reg (tailIndex encoding) : Operand 64).read s + BitVec.ofNat 64 (displacement encoding)) 1
  codeApart : RangeApart (rspOf s + (Operand.reg (tailIndex encoding) : Operand 64).read s + BitVec.ofNat 64 (displacement encoding)) 1 p (bytesAt encoding).length

def effectAt (p : BitVec 64) (encoding : Fin 9) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (bytesAt encoding).length
    writes := [⟨(.mem (rspOf s + (Operand.reg (tailIndex encoding) : Operand 64).read s + BitVec.ofNat 64 (displacement encoding)) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg (tailIndex encoding) : Operand 64).read s + BitVec.ofNat 64 (displacement encoding + 1)⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg (paddingIndex encoding) : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem run_at [Bindings] (p : BitVec 64) (encoding : Fin 9)
    (boundary : ReturnBoundary)
    (away : ∀ n : Nat, n ≤ 25 → p + BitVec.ofNat 64 n ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => PreAt p encoding s)
      (codeRange p (bytesAt encoding)) (Effect.post (effectAt p encoding)) := by
  have cases : encoding = 0 ∨ encoding = 1 ∨ encoding = 2 ∨ encoding = 3 ∨ encoding = 4 ∨ encoding = 5 ∨ encoding = 6 ∨ encoding = 7 ∨ encoding = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 13) 0 (.d8 32)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (0 : Fin 9).val = 0 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (0 : Fin 9).val = 0 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (0 : Fin 9).val = 0 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 6 (by omega)
    advance_then (lea_r64_effect_step (p + 6) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 10 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm8_effect_step (p + 10) 0x48 0xc7 33 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 14 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 14) 2 6 6) from xor_r32_r32_effect_step (p + 14) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 16 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 16) 2 3) from mov_r64_r64_effect_step (p + 16) 0x48 0xda (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 19 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (0 : Fin 9).val = 0 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (mov_m8_imm8_effect_step p (.sib 4 (some 5) 0 .none) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (1 : Fin 9).val = 1 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (1 : Fin 9).val = 1 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (1 : Fin 9).val = 1 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 5) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (StepEffect.forgetFlags (h := inc_r64_effect_step (p + 8) 0x48 0xc7 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, incR64Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 11 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 11) 2 6 6) from xor_r32_r32_effect_step (p + 11) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 13 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 13) 2 15) from mov_r64_r64_effect_step (p + 13) 0x4c 0xfa (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 16 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (1 : Fin 9).val = 1 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (mov_m8_imm8_effect_step p (.sib 4 (some 5) 0 .none) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (2 : Fin 9).val = 2 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (2 : Fin 9).val = 2 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (2 : Fin 9).val = 2 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 5) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (StepEffect.forgetFlags (h := inc_r64_effect_step (p + 8) 0x48 0xc7 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, incR64Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 11 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 11) 2 6 6) from xor_r32_r32_effect_step (p + 11) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 13 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 13) 2 3) from mov_r64_r64_effect_step (p + 13) 0x48 0xda (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 16 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (2 : Fin 9).val = 2 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 12) 0 .none) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (3 : Fin 9).val = 3 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (3 : Fin 9).val = 3 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (3 : Fin 9).val = 3 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (3 : Fin 9).val = 3 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 5 (by omega)
    advance_then (lea_r64_effect_step (p + 5) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 9 (by omega)
    advance_then (StepEffect.forgetFlags (h := inc_r64_effect_step (p + 9) 0x48 0xc7 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, incR64Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 12 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 12) 2 6 6) from xor_r32_r32_effect_step (p + 12) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 14 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 14) 2 3) from mov_r64_r64_effect_step (p + 14) 0x48 0xda (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 17 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (3 : Fin 9).val = 3 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 13) 0 (.d8 16)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (4 : Fin 9).val = 4 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (4 : Fin 9).val = 4 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (4 : Fin 9).val = 4 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (4 : Fin 9).val = 4 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 6 (by omega)
    advance_then (lea_r64_effect_step (p + 6) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 10 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm8_effect_step (p + 10) 0x48 0xc7 17 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 14 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 14) 2 6 6) from xor_r32_r32_effect_step (p + 14) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 16 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 16) 2 3) from mov_r64_r64_effect_step (p + 16) 0x48 0xda (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 19 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (4 : Fin 9).val = 4 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 13) 0 (.d32 240)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (5 : Fin 9).val = 5 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (5 : Fin 9).val = 5 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (5 : Fin 9).val = 5 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (5 : Fin 9).val = 5 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 9 (by omega)
    advance_then (lea_r64_effect_step (p + 9) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 13 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm32_effect_step (p + 13) 0x48 0xc7 241 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 20 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 20) 2 6 6) from xor_r32_r32_effect_step (p + 20) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 22 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 22) 2 14) from mov_r64_r64_effect_step (p + 22) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 25 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (5 : Fin 9).val = 5 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 13) 0 (.d32 256)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (6 : Fin 9).val = 6 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (6 : Fin 9).val = 6 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (6 : Fin 9).val = 6 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (6 : Fin 9).val = 6 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 9 (by omega)
    advance_then (lea_r64_effect_step (p + 9) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 13 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm32_effect_step (p + 13) 0x48 0xc7 257 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 20 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 20) 2 6 6) from xor_r32_r32_effect_step (p + 20) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 22 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 22) 2 14) from mov_r64_r64_effect_step (p + 22) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 25 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (6 : Fin 9).val = 6 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 12) 0 (.d32 256)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (7 : Fin 9).val = 7 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (7 : Fin 9).val = 7 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (7 : Fin 9).val = 7 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (7 : Fin 9).val = 7 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 9 (by omega)
    advance_then (lea_r64_effect_step (p + 9) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 13 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm32_effect_step (p + 13) 0x48 0xc7 257 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 20 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 20) 2 6 6) from xor_r32_r32_effect_step (p + 20) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 22 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 22) 2 3) from mov_r64_r64_effect_step (p + 22) 0x48 0xda (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 25 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (7 : Fin 9).val = 7 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · advance_begin (Sha2.Proofs.Wrapper.Hash.Padding.mov_m8_imm8_rex_effect_step p 0x42 (by simp [RexNoWPrefix]) (.sib 4 (some 13) 0 (.d8 32)) (by decide) rfl rfl 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm
        simpa [(show (8 : Fin 9).val = 8 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.writable
      · x86_norm
        intro j hj k hk
        simpa [(show (8 : Fin 9).val = 8 from rfl), tailIndex, displacement, rspOf, BitVec.add_assoc] using h.codeApart j hj k (by simp [bytesAt, (show (8 : Fin 9).val = 8 from rfl)]; omega)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [(show (8 : Fin 9).val = 8 from rfl), tailIndex, displacement, bytesAt, rspOf, BitVec.add_assoc] using h.codeApart
    case «next» => exact fun _ _ => away 6 (by omega)
    advance_then (lea_r64_effect_step (p + 6) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 10 (by omega)
    advance_then (StepEffect.forgetFlags (h := add_r64_imm8_effect_step (p + 10) 0x48 0xc7 33 (by simp [RexWPrefix]) rfl rfl))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 14 (by omega)
    advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect (p + 14) 2 6 6) from xor_r32_r32_effect_step (p + 14) 0xf6 rfl)))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component]) _, ?_⟩
      x86_norm
      exact away 16 (by omega)
    advance_then (show StepEffect _ _ (movR64R64Effect (p + 16) 2 14) from mov_r64_r64_effect_step (p + 16) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 19 (by omega)
    advance_finish [effectAt, tailIndex, paddingIndex, displacement, bytesAt, (show (8 : Fin 9).val = 8 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]

def encoding (v : Variant) (form : Form) : Fin 9 :=
  match form with
  | .slices => 0
  | .digest => 1
  | .reset stage => if stage.val = 2 then 3 else 2
  | .finalizeIntoReset second => if second then 5 else 4
  | .traitFinalizeIntoReset second => if second then 8 else if v = .sha512 then 7 else 6

abbrev Pre (v : Variant) (s : RamState) (form : Form := .slices) : Prop :=
  PreAt (v.pc (setupOffset v form) form) (encoding v form) s

def effect (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  effectAt (v.pc (setupOffset v form) form) (encoding v form) s

theorem code {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
    (eligible : form.canFinalize) :
    CodeIn (codeRange (v.pc (setupOffset v form) form) (bytesAt (encoding v form))) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + setupOffset v form) (bytesAt (encoding v form))
  all_goals cases form <;> cases v <;>
    simp only [setupOffset, encoding, Form.canFinalize, Variant.textOffset, reduceCtorEq, reduceIte] at * <;>
    (repeat' split) <;> decide +kernel

set_option maxHeartbeats 2000000 in
theorem run [Bindings] {v : Variant} {form : Form} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre v s form)
      (codeRange (v.pc (setupOffset v form) form) (bytesAt (encoding v form)))
      (Effect.post (fun s => effect v s form)) := by
  apply run_at
  intro n hn
  rw [Variant.pc_add (form := form)]
  apply boundary_ne_program outside
  apply inProgram_of_textOffset
  change v.textOffset form + (setupOffset v form + n) < 71757
  cases form <;> cases v <;> simp only [Variant.textOffset, setupOffset] <;>
    (repeat' split) <;> omega

theorem endOffset (v : Variant) (form : Form) :
    setupOffset v form + (bytesAt (encoding v form)).length = fillOffset v form := by
  cases form <;> cases v <;>
    simp only [setupOffset, encoding, fillOffset, reduceCtorEq, reduceIte] <;> (repeat' split) <;> decide +kernel

theorem effect_rip (v : Variant) (s : RamState) (form : Form) :
    (effect v s form).rip = v.pc (fillOffset v form) form := by
  simp only [effect, effectAt, Variant.pc_add, endOffset]

theorem code_bound (v : Variant) (form : Form) :
    v.textOffset form + setupOffset v form + (bytesAt (encoding v form)).length ≤ 71757 := by
  rw [Nat.add_assoc, endOffset]
  cases form <;> cases v <;> simp only [Variant.textOffset, fillOffset] <;>
    (repeat' split) <;> decide +kernel

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.FillSetup
