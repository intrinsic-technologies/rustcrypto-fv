import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.ResetLayout
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

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def copySetupBytes (form : Form := .slices) (v : Variant := .sha384) : List UInt8 :=
  match form with
  | .slices => [72, 141, 156, 36, 200, 1, 0, 0, 72, 141, 116, 36, 32, 186, 128, 0, 0, 0, 72, 137, 223]
  | .digest => [76, 141, 188, 36, 168, 1, 0, 0, 72, 137, 230, 186, 128, 0, 0, 0, 76, 137, 255]
  | .reset _ => [72, 141, 156, 36, 248, 0, 0, 0, 72, 137, 230, 186, 128, 0, 0, 0, 72, 137, 223]
  | .finalizeIntoReset false => [72, 141, 156, 36, 240, 0, 0, 0, 72, 141, 116, 36, 16, 186, 128, 0, 0, 0, 72, 137, 223]
  | .finalizeIntoReset true => [76, 141, 180, 36, 200, 1, 0, 0, 72, 141, 180, 36, 240, 0, 0, 0, 186, 128, 0, 0, 0, 76, 137, 247]
  | .traitFinalizeIntoReset false => if v = .sha512 then [72, 141, 92, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 72, 137, 223] else [76, 141, 116, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 76, 137, 247]
  | .traitFinalizeIntoReset true => [76, 141, 180, 36, 216, 1, 0, 0, 72, 141, 116, 36, 32, 186, 128, 0, 0, 0, 76, 137, 247]

def copySetupLength (form : Form) (v : Variant := .sha384) : Nat :=
  (copySetupBytes form v).length

def copySetupEffect (p : BitVec 64) (s : RamState) (form : Form := .slices) (v : Variant := .sha384) : Effect :=
  match form with
  | .slices =>
    { rip := p + 21
      writes := [⟨(.reg 3 : Operand 64), rspOf s + 456⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 32⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 456⟩] }
  | .digest =>
    { rip := p + 19
      writes := [⟨(.reg 15 : Operand 64), rspOf s + 424⟩,
        ⟨(.reg 6 : Operand 64), rspOf s⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 424⟩] }
  | .reset _ =>
    { rip := p + 19
      writes := [⟨(.reg 3 : Operand 64), rspOf s + 248⟩,
        ⟨(.reg 6 : Operand 64), rspOf s⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 248⟩] }
  | .finalizeIntoReset false =>
    { rip := p + 21
      writes := [⟨(.reg 3 : Operand 64), rspOf s + 240⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 16⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 240⟩] }
  | .finalizeIntoReset true =>
    { rip := p + 24
      writes := [⟨(.reg 14 : Operand 64), rspOf s + 456⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 240⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 456⟩] }
  | .traitFinalizeIntoReset false =>
    if v = .sha512 then
    { rip := p + 21
      writes := [⟨(.reg 3 : Operand 64), rspOf s + 32⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 256⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 32⟩] }
    else
    { rip := p + 21
      writes := [⟨(.reg 14 : Operand 64), rspOf s + 32⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 256⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 32⟩] }
  | .traitFinalizeIntoReset true =>
    { rip := p + 21
      writes := [⟨(.reg 14 : Operand 64), rspOf s + 472⟩,
        ⟨(.reg 6 : Operand 64), rspOf s + 32⟩,
        ⟨(.reg 2 : Operand 64), 128⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + 472⟩] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem copySetup [Bindings] {form : Form} (p : BitVec 64) (boundary : ReturnBoundary) (v : Variant)
    (nextState : ∀ i : Nat, i ≤ copySetupLength form v → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (copySetupBytes form v))
      (Effect.post (fun s => copySetupEffect p s form v)) := by
  cases form with
  | slices =>
    simp only [copySetupLength, copySetupBytes] at nextState ⊢
    advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
    case «next» => exact fun _ _ => nextState 8 (by decide)
    advance_then (lea_r64_effect_step (p+8) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.slices)) 8 5)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 13 (by decide)
    advance_then (mov_r32_imm32_effect_step (p+13) 0xba (by decide) 128)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.slices)) 13 5)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 18 (by decide)
    advance_then (mov_r64_r64_effect_step (p+18) 0x48 0xdf (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.slices)) 18 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 21 (by decide)
    advance_finish [copySetupEffect]
  | digest =>
    simp only [copySetupLength, copySetupBytes] at nextState ⊢
    advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 15
      (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
    case «next» => exact fun _ _ => nextState 8 (by decide)
    advance_then (mov_r64_r64_effect_step (p+8) 0x48 0xe6 (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.digest)) 8 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 11 (by decide)
    advance_then (mov_r32_imm32_effect_step (p+11) 0xba (by decide) 128)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.digest)) 11 5)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 16 (by decide)
    advance_then (mov_r64_r64_effect_step (p+16) 0x4c 0xff (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.digest)) 16 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 19 (by decide)
    advance_finish [copySetupEffect]
  | reset stage =>
    simp only [copySetupLength, copySetupBytes] at nextState ⊢
    advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
    case «next» => exact fun _ _ => nextState 8 (by decide)
    advance_then (mov_r64_r64_effect_step (p+8) 0x48 0xe6 (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.reset stage)) 8 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 11 (by decide)
    advance_then (mov_r32_imm32_effect_step (p+11) 0xba (by decide) 128)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.reset stage)) 11 5)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 16 (by decide)
    advance_then (mov_r64_r64_effect_step (p+16) 0x48 0xdf (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p (copySetupBytes (.reset stage)) 16 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 19 (by decide)
    advance_finish [copySetupEffect]
  | finalizeIntoReset second =>
    cases second with
    | false =>
      simp only [copySetupLength, copySetupBytes] at nextState ⊢
      advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 3
        (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
      case «next» => exact fun _ _ => nextState 8 (by decide)
      advance_then (lea_r64_effect_step (p+8) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset false)) 8 5)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 13 (by decide)
      advance_then (mov_r32_imm32_effect_step (p+13) 0xba (by decide) 128)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset false)) 13 5)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 18 (by decide)
      advance_then (mov_r64_r64_effect_step (p+18) 0x48 0xdf (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset false)) 18 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 21 (by decide)
      advance_finish [copySetupEffect]
    | true =>
      simp only [copySetupLength, copySetupBytes] at nextState ⊢
      advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 14
        (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
      case «next» => exact fun _ _ => nextState 8 (by decide)
      advance_then (lea_r64_effect_step (p+8) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset true)) 8 8)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 16 (by decide)
      advance_then (mov_r32_imm32_effect_step (p+16) 0xba (by decide) 128)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset true)) 16 5)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 21 (by decide)
      advance_then (mov_r64_r64_effect_step (p+21) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.finalizeIntoReset true)) 21 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 24 (by decide)
      advance_finish [copySetupEffect]
  | traitFinalizeIntoReset second =>
    cases second with
    | false =>
      by_cases hv : v = .sha512
      · simp only [copySetupLength, copySetupBytes, hv] at nextState ⊢
        advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 3
          (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (lea_r64_effect_step (p+5) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl)
        try (case sub => exact codeRange_slice_subset p ([72, 141, 92, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 72, 137, 223] : List UInt8) 5 8)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 13 (by decide)
        advance_then (mov_r32_imm32_effect_step (p+13) 0xba (by decide) 128)
        try (case sub => exact codeRange_slice_subset p ([72, 141, 92, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 72, 137, 223] : List UInt8) 13 5)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 18 (by decide)
        advance_then (mov_r64_r64_effect_step (p+18) 0x48 0xdf (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p ([72, 141, 92, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 72, 137, 223] : List UInt8) 18 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 21 (by decide)
        advance_finish [copySetupEffect, hv]
      · simp only [copySetupLength, copySetupBytes, hv, ite_false] at nextState ⊢
        advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 14
          (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (lea_r64_effect_step (p+5) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl)
        try (case sub => exact codeRange_slice_subset p ([76, 141, 116, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 76, 137, 247] : List UInt8) 5 8)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 13 (by decide)
        advance_then (mov_r32_imm32_effect_step (p+13) 0xba (by decide) 128)
        try (case sub => exact codeRange_slice_subset p ([76, 141, 116, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 76, 137, 247] : List UInt8) 13 5)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 18 (by decide)
        advance_then (mov_r64_r64_effect_step (p+18) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p ([76, 141, 116, 36, 32, 72, 141, 180, 36, 0, 1, 0, 0, 186, 128, 0, 0, 0, 76, 137, 247] : List UInt8) 18 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 21 (by decide)
        advance_finish [copySetupEffect, hv]
    | true =>
      simp only [copySetupLength, copySetupBytes] at nextState ⊢
      advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 14
        (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl)
      case «next» => exact fun _ _ => nextState 8 (by decide)
      advance_then (lea_r64_effect_step (p+8) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.traitFinalizeIntoReset true)) 8 5)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 13 (by decide)
      advance_then (mov_r32_imm32_effect_step (p+13) 0xba (by decide) 128)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.traitFinalizeIntoReset true)) 13 5)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 18 (by decide)
      advance_then (mov_r64_r64_effect_step (p+18) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p (copySetupBytes (.traitFinalizeIntoReset true)) 18 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 21 (by decide)
      advance_finish [copySetupEffect]

def setupBytes (form : Form := .slices) (last : Bool := false) (v : Variant := .sha384) : List UInt8 :=
  match form with
  | .slices => [186, 1, 0, 0, 0, 76, 137, 247, 72, 137, 222]
  | .digest => [186, 1, 0, 0, 0, 76, 137, 247, 76, 137, 254]
  | .reset stage => if stage.val ≠ 2 ∧ last = true then [186, 1, 0, 0, 0, 76, 141, 180, 36, 128, 0, 0, 0, 76, 137, 247, 72, 137, 222] else [186, 1, 0, 0, 0, 72, 141, 188, 36, 128, 0, 0, 0, 72, 137, 222]
  | .finalizeIntoReset false => if last then [186, 1, 0, 0, 0, 76, 141, 180, 36, 144, 0, 0, 0, 76, 137, 247, 72, 137, 222] else [186, 1, 0, 0, 0, 72, 141, 188, 36, 144, 0, 0, 0, 72, 137, 222]
  | .finalizeIntoReset true => [186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246]
  | .traitFinalizeIntoReset false => if v = .sha512 then [186, 1, 0, 0, 0, 72, 137, 239, 72, 137, 222] else [186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246]
  | .traitFinalizeIntoReset true => [186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246]

def setupLength (form : Form) (last : Bool) (v : Variant) : Nat :=
  (setupBytes form last v).length

def setupEffect (p : BitVec 64) (s : RamState) (form : Form := .slices)
    (last : Bool := false) (v : Variant := .sha384) : Effect :=
  match form with
  | .slices => { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .r14⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] }
  | .digest => { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .r14⟩, ⟨(.reg 6 : Operand 64), s.regValue .r15⟩] }
  | .reset stage => if stage.val ≠ 2 ∧ last = true then { rip := p + 19, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 14 : Operand 64), rspOf s + 128⟩, ⟨(.reg 7 : Operand 64), rspOf s + 128⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] } else { rip := p + 16, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), rspOf s + 128⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] }
  | .finalizeIntoReset false => if last then { rip := p + 19, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 14 : Operand 64), rspOf s + 144⟩, ⟨(.reg 7 : Operand 64), rspOf s + 144⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] } else { rip := p + 16, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), rspOf s + 144⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] }
  | .finalizeIntoReset true => { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .rbx⟩, ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }
  | .traitFinalizeIntoReset false => if v = .sha512 then { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .rbp⟩, ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] } else { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .rbx⟩, ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }
  | .traitFinalizeIntoReset true => { rip := p + 11, writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), s.regValue .rbx⟩, ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem setup [Bindings] {form : Form} (p : BitVec 64) (boundary : ReturnBoundary)
    (last : Bool) (v : Variant)
    (nextState : ∀ i : Nat, i ≤ setupLength form last v → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (setupBytes form last v))
      (Effect.post (fun s => setupEffect p s form last v)) := by
  cases form with
  | slices =>
    simp only [setupLength, setupBytes] at nextState ⊢
    advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 0 5)
    case «next» => exact fun _ _ => nextState 5 (by decide)
    advance_then (mov_r64_r64_effect_step (p+5) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 5 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 8 (by decide)
    advance_then (mov_r64_r64_effect_step (p+8) 0x48 0xde (by simp [RexWPrefix]) rfl)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 8 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 11 (by decide)
    advance_finish [setupEffect]
  | digest =>
    simp only [setupLength, setupBytes] at nextState ⊢
    advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 76, 137, 254] : List UInt8) 0 5)
    case «next» => exact fun _ _ => nextState 5 (by decide)
    advance_then (mov_r64_r64_effect_step (p+5) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 76, 137, 254] : List UInt8) 5 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 8 (by decide)
    advance_then (mov_r64_r64_effect_step (p+8) 0x4c 0xfe (by simp [RexWPrefix]) rfl)
    try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 137, 247, 76, 137, 254] : List UInt8) 8 3)
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact nextState 11 (by decide)
    advance_finish [setupEffect]
  | reset stage =>
    by_cases hs : stage.val ≠ 2 ∧ last = true
    ·
      simp only [setupLength, setupBytes] at nextState ⊢
      rw [ite_eq_left hs] at nextState ⊢
      advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 128, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 0 5)
      case «next» => exact fun _ _ => nextState 5 (by decide)
      advance_then (lea_r64_effect_step (p+5) 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 128, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 5 8)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 13 (by decide)
      advance_then (mov_r64_r64_effect_step (p+13) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 128, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 13 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 16 (by decide)
      advance_then (mov_r64_r64_effect_step (p+16) 0x48 0xde (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 128, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 16 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 19 (by decide)
      advance_finish [setupEffect, hs.1, hs.2]
    ·
      simp only [setupLength, setupBytes, hs, ite_false] at nextState ⊢
      advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 128, 0, 0, 0, 72, 137, 222] : List UInt8) 0 5)
      case «next» => exact fun _ _ => nextState 5 (by decide)
      advance_then (lea_r64_effect_step (p+5) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 128, 0, 0, 0, 72, 137, 222] : List UInt8) 5 8)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 13 (by decide)
      advance_then (mov_r64_r64_effect_step (p+13) 0x48 0xde (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 128, 0, 0, 0, 72, 137, 222] : List UInt8) 13 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 16 (by decide)
      advance_finish [setupEffect, hs]
  | finalizeIntoReset second =>
    cases second with
    | false =>
      cases last with
      | false =>
        simp only [setupLength, setupBytes] at nextState ⊢
        advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 144, 0, 0, 0, 72, 137, 222] : List UInt8) 0 5)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (lea_r64_effect_step (p+5) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 144, 0, 0, 0, 72, 137, 222] : List UInt8) 5 8)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 13 (by decide)
        advance_then (mov_r64_r64_effect_step (p+13) 0x48 0xde (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 141, 188, 36, 144, 0, 0, 0, 72, 137, 222] : List UInt8) 13 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 16 (by decide)
        advance_finish [setupEffect]
      | true =>
        simp only [setupLength, setupBytes, ite_true] at nextState ⊢
        advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 144, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 0 5)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (lea_r64_effect_step (p+5) 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 144, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 5 8)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 13 (by decide)
        advance_then (mov_r64_r64_effect_step (p+13) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 144, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 13 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 16 (by decide)
        advance_then (mov_r64_r64_effect_step (p+16) 0x48 0xde (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 76, 141, 180, 36, 144, 0, 0, 0, 76, 137, 247, 72, 137, 222] : List UInt8) 16 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 19 (by decide)
        advance_finish [setupEffect]
    | true =>
      simp only [setupLength, setupBytes] at nextState ⊢
      advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 0 5)
      case «next» => exact fun _ _ => nextState 5 (by decide)
      advance_then (mov_r64_r64_effect_step (p+5) 0x48 0xdf (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 5 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 8 (by decide)
      advance_then (mov_r64_r64_effect_step (p+8) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 8 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 11 (by decide)
      advance_finish [setupEffect]
  | traitFinalizeIntoReset second =>
    cases second with
    | false =>
      by_cases hv : v = .sha512
      ·
        simp only [setupLength, setupBytes, hv, ite_true] at nextState ⊢
        advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 239, 72, 137, 222] : List UInt8) 0 5)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (mov_r64_r64_effect_step (p+5) 0x48 0xef (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 239, 72, 137, 222] : List UInt8) 5 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p+8) 0x48 0xde (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 239, 72, 137, 222] : List UInt8) 8 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 11 (by decide)
        advance_finish [setupEffect, hv]
      ·
        simp only [setupLength, setupBytes, hv, ite_false] at nextState ⊢
        advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 0 5)
        case «next» => exact fun _ _ => nextState 5 (by decide)
        advance_then (mov_r64_r64_effect_step (p+5) 0x48 0xdf (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 5 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p+8) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
        try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 8 3)
        case mid =>
          intro s t hP hH hO
          refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          x86_norm
          exact nextState 11 (by decide)
        advance_finish [setupEffect, hv]
    | true =>
      simp only [setupLength, setupBytes] at nextState ⊢
      advance_begin (mov_r32_imm32_effect_step p 0xba (by decide) 1)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 0 5)
      case «next» => exact fun _ _ => nextState 5 (by decide)
      advance_then (mov_r64_r64_effect_step (p+5) 0x48 0xdf (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 5 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 8 (by decide)
      advance_then (mov_r64_r64_effect_step (p+8) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
      try (case sub => simpa only [BitVec.add_zero] using codeRange_slice_subset p ([186, 1, 0, 0, 0, 72, 137, 223, 76, 137, 246] : List UInt8) 8 3)
      case mid =>
        intro s t hP hH hO
        refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact nextState 11 (by decide)
      advance_finish [setupEffect]

def callOffset (v : Variant) (form : Form) (last : Bool) : Nat :=
  match form with
  | .slices => if last then 0x379 else 0x2a1
  | .digest => if last then 0x28a else 0x1c1
  | .reset stage => (ResetLayout.reset v).padCalls[
      if stage.val = 2 then (if last then 3 else 2) else (if last then 1 else 0)]!
  | .finalizeIntoReset second => (ResetLayout.finalizeIntoReset v).padCalls[
      if second then (if last then 3 else 2) else (if last then 1 else 0)]!
  | .traitFinalizeIntoReset second => (ResetLayout.traitFinalizeIntoReset v).padCalls[
      if second then (if last then 3 else 2) else (if last then 1 else 0)]!

def setupOffset (v : Variant) (form : Form) (last : Bool) : Nat :=
  callOffset v form last - setupLength form last v

def copySetupOffset (v : Variant) (form : Form) (last : Bool) : Nat :=
  setupOffset v form last - 6 - copySetupLength form v

theorem copySetupCode {form : Form} {v : Variant} (last : Bool) {s : RamState}
    (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (copySetupOffset v form last) form) (copySetupBytes form v)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + copySetupOffset v form last) (copySetupBytes form v)
  · cases form <;> cases v <;> cases last <;> decide +revert +kernel
  · cases form <;> cases v <;> cases last <;> decide +revert +kernel

theorem setupCode {form : Form} {v : Variant} (last : Bool) {s : RamState}
    (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (setupOffset v form last) form) (setupBytes form last v)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + setupOffset v form last) (setupBytes form last v)
  · cases form <;> cases v <;> cases last <;> decide +revert +kernel
  · cases form <;> cases v <;> cases last <;> decide +revert +kernel

end Sha2.Proofs.Wrapper512.Hash.Finalize.Compress
