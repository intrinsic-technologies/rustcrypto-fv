import Sha2.Proofs.Wrapper512.Dispatch.Store
import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Machine
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.Instructions.ShiftLeft.Compose
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Branch.Triple
import Sha2.Proofs.Common.Instructions.XorImmediate
import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.EffectCompose.Advance
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.Variant
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

abbrev setupOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x258
  | .digest => 0x17d
  | .reset stage => if stage.val = 2 then (match v with | .sha384 => 0x74c | .sha512 => 0x76c | .sha512_224 => 0x72c | .sha512_256 => 0x72c) else 0x406
  | .finalizeIntoReset second => if second then (match v with | .sha384 => 0x5aa | .sha512 => 0x5ca | .sha512_224 => 0x58c | .sha512_256 => 0x58c) else 0x237
  | .traitFinalizeIntoReset second => if second then (match v with | .sha384 => 0x672 | .sha512 => 0x692 | .sha512_224 => 0x652 | .sha512_256 => 0x652) else 0x29c

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate

abbrev startOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x230
  | .finalizeIntoReset true => match v with
    | .sha384 => 0x582 | .sha512 => 0x5a2 | _ => 0x564
  | .traitFinalizeIntoReset true => match v with
    | .sha384 => 0x64a | .sha512 => 0x66a | _ => 0x62a
  | _ => 0x159

abbrev hashOffset (form : Form) : Nat :=
  match form with
  | .slices | .traitFinalizeIntoReset true => 160
  | .finalizeIntoReset true => 368
  | _ => 128

abbrev hashReg (form : Form) : Fin 16 :=
  match form with
  | .finalizeIntoReset true | .traitFinalizeIntoReset true => 3
  | _ => 14

abbrev tailReg (form : Form) : Fin 16 := if form = .digest then 5 else 13
abbrev lowReg (form : Form) : Fin 16 := if form = .digest then 13 else 12
abbrev highReg (form : Form) : Fin 16 := if form = .digest then 12 else 15
abbrev padReg (form : Form) : Fin 16 :=
  match form with
  | .slices => 3
  | .digest => 15
  | _ => 14

structure Pre (v : Variant) (s : RamState) (form : Form := .slices) : Prop where
  rip : s.RIP = (v.pc (startOffset v form) form)
  tailLength : MemReadable s (rspOf s + BitVec.ofNat 64 (hashOffset form - 1)) 1
  blocks : MemReadable s (rspOf s + BitVec.ofNat 64 (hashOffset form + 64)) 8
  blocksHigh : MemReadable s (rspOf s + BitVec.ofNat 64 (hashOffset form + 72)) 8

def bytes (form : Form := .slices) : List UInt8 :=
  match form with
  | .slices =>
    [0x4c,0x8d,0xb4,0x24,0xa0,0x0,0x0,0x0,0x44,0xf,0xb6,0xac,0x24,0x9f,0x0,0x0,0x0,0x4c,0x8b,0xa4,0x24,0xe0,0x0,0x0,0x0,0x4c,0x8b,0xbc,0x24,0xe8,0x0,0x0,0x0,0x4c,0x89,0xeb,0x48,0x83,0xf3,0x7f]

  | .finalizeIntoReset true => [0x48,0x8d,0x9c,0x24,0x70,0x01,0x00,0x00,0x44,0x0f,0xb6,0xac,0x24,0x6f,0x01,0x00,0x00,0x4c,0x8b,0xa4,0x24,0xb0,0x01,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xb8,0x01,0x00,0x00,0x4d,0x89,0xee,0x49,0x83,0xf6,0x7f]
  | .traitFinalizeIntoReset true => [0x48,0x8d,0x9c,0x24,0xa0,0x00,0x00,0x00,0x44,0x0f,0xb6,0xac,0x24,0x9f,0x00,0x00,0x00,0x4c,0x8b,0xa4,0x24,0xe0,0x00,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xe8,0x00,0x00,0x00,0x4d,0x89,0xee,0x49,0x83,0xf6,0x7f]
  | _ => [0x4c,0x8d,0xb4,0x24,0x80,0x0,0x0,0x0,0xf,0xb6,0x6c,0x24,0x7f,0x4c,0x8b,0xac,0x24,0xc0,0x0,0x0,0x0,0x4c,0x8b,0xa4,0x24,0xc8,0x0,0x0,0x0,0x49,0x89,0xef,0x49,0x83,0xf7,0x7f]

def effect (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  { rip := (v.pc (startOffset v form + (if form = .digest then 36 else 40)) form)
    writes := [⟨(.reg (hashReg form) : Operand 64), rspOf s + BitVec.ofNat 64 (hashOffset form)⟩,
      ⟨(.reg (tailReg form) : Operand 64), (memLoad s.external (rspOf s + BitVec.ofNat 64 (hashOffset form - 1)) 8).setWidth 64⟩,
      ⟨(.reg (lowReg form) : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (hashOffset form + 64)) 64⟩,
      ⟨(.reg (highReg form) : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (hashOffset form + 72)) 64⟩,
      ⟨(.reg (padReg form) : Operand 64), (memLoad s.external (rspOf s + BitVec.ofNat 64 (hashOffset form - 1)) 8).setWidth 64 ^^^ 127⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
    (eligible : form = .slices ∨ form = .digest ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true := by first | assumption | simp) :
    CodeIn (codeRange (v.pc (startOffset v form) form) (bytes form)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + (startOffset v form)) (bytes form)
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel

macro "load_clone_run" f:term:max v:term:max base:term:max disp:term:max hashRex:term:max hashDest:term:max moveRex:term:max moveMod:term:max xorRex:term:max xorMod:term:max boundary:term:max outside:term:max : tactic =>
  `(tactic| (
    advance_begin (lea_r64_effect_step (($v).pc ($base + 0) $f)  $hashRex (by simp [RexWPrefix]) $hashDest
      (.sib 4 none 0 (.d32 $disp)) (by decide) rfl rfl)
    case «next» =>
      intro _ _
      change ($v).pc ($base + 0) $f + BitVec.ofNat 64 8 ≠ ($boundary).rip
      rw [Variant.pc_add (form := $f)]
      exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))
    advance_then (movzx_r_m8_rex_effect_step (($v).pc ($base + 8) $f) 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
        (fun _ => rfl) 5 (.sib 4 none 0 (.d32 ($disp - 1))) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add $v ($base + 0) 8 $f]
      exact codeRange_slice_subset (($v).pc ($base + 0) $f) (bytes $f) 8 9
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := $f)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change ($v).pc ($base + 8) $f + BitVec.ofNat 64 9 ≠ ($boundary).rip
          rw [Variant.pc_add (form := $f)]
          exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))⟩
      x86_norm
      exact hp.tailLength
    advance_then (mov_r64_m64_effect_step (($v).pc ($base + 17) $f) 0x4c (by simp [RexWPrefix]) 4
        (.sib 4 none 0 (.d32 ($disp + 64))) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add $v ($base + 0) 17 $f]
      exact codeRange_slice_subset (($v).pc ($base + 0) $f) (bytes $f) 17 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := $f)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change ($v).pc ($base + 17) $f + BitVec.ofNat 64 8 ≠ ($boundary).rip
          rw [Variant.pc_add (form := $f)]
          exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))⟩
      x86_norm
      exact hp.blocks
    advance_then (mov_r64_m64_effect_step (($v).pc ($base + 25) $f) 0x4c (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d32 ($disp + 72))) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add $v ($base + 0) 25 $f]
      exact codeRange_slice_subset (($v).pc ($base + 0) $f) (bytes $f) 25 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := $f)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change ($v).pc ($base + 25) $f + BitVec.ofNat 64 8 ≠ ($boundary).rip
          rw [Variant.pc_add (form := $f)]
          exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))⟩
      x86_norm
      exact hp.blocksHigh
    advance_then (mov_r64_r64_effect_step (($v).pc ($base + 33) $f)  $moveRex $moveMod (by simp [RexWPrefix]) rfl)
    case sub =>
      rw [← Variant.pc_add $v ($base + 0) 33 $f]
      exact codeRange_slice_subset (($v).pc ($base + 0) $f) (bytes $f) 33 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by simp only [Variant.pc_add (form := $f)]),
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change ($v).pc ($base + 33) $f + BitVec.ofNat 64 3 ≠ ($boundary).rip
          rw [Variant.pc_add (form := $f)]
          exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))⟩
    advance_then (StepEffect.forgetFlags (h := xor_r64_imm8_effect_step (($v).pc ($base + 36) $f)  $xorRex $xorMod 127 (by simp [RexWPrefix]) rfl rfl))
    case sub =>
      rw [← Variant.pc_add $v ($base + 0) 36 $f]
      exact codeRange_slice_subset (($v).pc ($base + 0) $f) (bytes $f) 36 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by simp only [Variant.pc_add (form := $f)]),
        Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component]) _,
        by
          change ($v).pc ($base + 36) $f + BitVec.ofNat 64 4 ≠ ($boundary).rip
          rw [Variant.pc_add (form := $f)]
          exact boundary_ne_program $outside (inProgram_of_textOffset _ (by cases ($v) <;> decide))⟩
    advance_finish [effect, hashOffset, hashReg, tailReg, lowReg, highReg, padReg, startOffset, Variant.pc_add (form := $f)]
  ))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem run [Bindings] {v : Variant} {form : Form} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (eligible : form = .slices ∨ form = .digest ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true := by first | assumption | simp) :
    AdvanceTriple boundary (fun s => Pre v s form) (codeRange (v.pc (startOffset v form) form) (bytes form)) (Effect.post (fun s => effect v s form)) := by
  rcases eligible with rfl | rfl | rfl | rfl
  ·
    load_clone_run (.slices) (v) (0x230) (160) (0x4c) (6) (0x4c) (0xeb) (0x48) (0xf3) (boundary) (outside)
  ·
    advance_begin (lea_r64_effect_step (v.pc 0x159 .digest) 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
    case «next» =>
      intro _ _
      change v.pc 0x159 .digest + BitVec.ofNat 64 8 ≠ boundary.rip
      rw [Variant.pc_add (form := .digest)]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x161 < 1024) .digest)
    advance_then (movzx_r32_m8_effect_step (v.pc 0x161 .digest) 5 (.sib 4 none 0 (.d8 127)) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add v 0x159 8 .digest]
      exact codeRange_slice_subset (v.pc 0x159 .digest) (bytes .digest) 8 5
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := .digest)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change v.pc 0x161 .digest + BitVec.ofNat 64 5 ≠ boundary.rip
          rw [Variant.pc_add (form := .digest)]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x166 < 1024) .digest)⟩
      x86_norm
      exact hp.tailLength
    advance_then (mov_r64_m64_effect_step (v.pc 0x166 .digest) 0x4c (by simp [RexWPrefix]) 5
        (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add v 0x159 13 .digest]
      exact codeRange_slice_subset (v.pc 0x159 .digest) (bytes .digest) 13 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := .digest)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change v.pc 0x166 .digest + BitVec.ofNat 64 8 ≠ boundary.rip
          rw [Variant.pc_add (form := .digest)]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x16e < 1024) .digest)⟩
      x86_norm
      exact hp.blocks
    advance_then (mov_r64_m64_effect_step (v.pc 0x16e .digest) 0x4c (by simp [RexWPrefix]) 4
        (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
    case sub =>
      rw [← Variant.pc_add v 0x159 21 .digest]
      exact codeRange_slice_subset (v.pc 0x159 .digest) (bytes .digest) 21 8
    case mid =>
      intro s t hp hh ho
      refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add (form := .digest)]) (by x86_addr_obs) ?_,
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change v.pc 0x16e .digest + BitVec.ofNat 64 8 ≠ boundary.rip
          rw [Variant.pc_add (form := .digest)]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x176 < 1024) .digest)⟩
      x86_norm
      exact hp.blocksHigh
    advance_then (mov_r64_r64_effect_step (v.pc 0x176 .digest) 0x49 0xef (by simp [RexWPrefix]) rfl)
    case sub =>
      rw [← Variant.pc_add v 0x159 29 .digest]
      exact codeRange_slice_subset (v.pc 0x159 .digest) (bytes .digest) 29 3
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by simp only [Variant.pc_add (form := .digest)]),
        Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by
          change v.pc 0x176 .digest + BitVec.ofNat 64 3 ≠ boundary.rip
          rw [Variant.pc_add (form := .digest)]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x179 < 1024) .digest)⟩
    advance_then (StepEffect.forgetFlags (h := xor_r64_imm8_effect_step (v.pc 0x179 .digest) 0x49 0xf7 127 (by simp [RexWPrefix]) rfl rfl))
    case sub =>
      rw [← Variant.pc_add v 0x159 32 .digest]
      exact codeRange_slice_subset (v.pc 0x159 .digest) (bytes .digest) 32 4
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by simp only [Variant.pc_add (form := .digest)]),
        Effect.Avoids.of_noMem (by simp [Component.Covers, Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component]) _,
        by
          change v.pc 0x179 .digest + BitVec.ofNat 64 4 ≠ boundary.rip
          rw [Variant.pc_add (form := .digest)]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x17d < 1024) .digest)⟩
    advance_finish [effect, hashOffset, hashReg, tailReg, lowReg, highReg, padReg, startOffset, Variant.pc_add (form := .digest)]
  · load_clone_run (.finalizeIntoReset true) (v) (startOffset v (.finalizeIntoReset true)) (368) (0x48) (3) (0x4d) (0xee) (0x49) (0xf6) (boundary) (outside)
  · load_clone_run (.traitFinalizeIntoReset true) (v) (startOffset v (.traitFinalizeIntoReset true)) (160) (0x48) (3) (0x4d) (0xee) (0x49) (0xf6) (boundary) (outside)

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate Sha2.Proofs.Common.Instructions.ShiftLeft
attribute [local x86_compose] Length.Shld.effect shlR64Effect
attribute [local x86_local] Length.Machine.shld_local

abbrev countStartOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .reset stage => if stage.val = 2 then (match v with
      | .sha384 => 0x719 | .sha512 => 0x739 | _ => 0x6f9) else 0x3b5
  | .finalizeIntoReset _ => 0x20b
  | _ => 0x256
abbrev countTailOffset (form : Form) : Nat :=
  match form with
  | .reset _ => 127
  | .finalizeIntoReset _ => 143
  | _ => 383
abbrev countLength (form : Form) : Nat :=
  match form with
  | .reset stage => if stage.val = 2 then 51 else 81
  | .finalizeIntoReset _ => 44
  | _ => 70
abbrev countLowReg (v : Variant) (form : Form) : BitVec 5 :=
  if form = .traitFinalizeIntoReset false ∧ v ≠ .sha512 then 15 else 14
abbrev countHighReg (v : Variant) (form : Form) : BitVec 5 :=
  match form with
  | .traitFinalizeIntoReset _ => if v = .sha512 then 15 else 12
  | .finalizeIntoReset _ => if v = .sha384 ∨ v = .sha512 then 15 else 12
  | _ => 15
abbrev countTailReg (v : Variant) (form : Form) : BitVec 5 :=
  match form with
  | .reset stage => if stage.val = 2 then 12 else 5
  | .traitFinalizeIntoReset _ => if v = .sha512 then 12 else 13
  | _ => 13
abbrev countPadReg (v : Variant) (form : Form) : BitVec 5 :=
  if form = .traitFinalizeIntoReset false ∧ v ≠ .sha512 then 14 else 3

structure CountPre (p : BitVec 64) (s : RamState) (form : Form) : Prop where
  rip : s.RIP = p
  tailLength : MemReadable s (rspOf s + BitVec.ofNat 64 (countTailOffset form)) 1
  blocks : MemReadable s (rspOf s + BitVec.ofNat 64 (countTailOffset form + 65)) 8
  blocksHigh : MemReadable s (rspOf s + BitVec.ofNat 64 (countTailOffset form + 73)) 8
  output : if form = .traitFinalizeIntoReset false then MemReadable s (rspOf s + 240) 8 else True

def countEffect (v : Variant) (p : BitVec 64) (s : RamState) (form : Form) : Effect :=
  let tail := (memLoad s.external (rspOf s + BitVec.ofNat 64 (countTailOffset form)) 8).setWidth 64
  let lo := memLoad s.external (rspOf s + BitVec.ofNat 64 (countTailOffset form + 65)) 64
  let hi := memLoad s.external (rspOf s + BitVec.ofNat 64 (countTailOffset form + 73)) 64
  { rip := p + BitVec.ofNat 64 (countLength form)
    writes := [⟨(.reg 0 : Operand 64), tail⟩,
      ⟨(.reg (countLowReg v form) : Operand 64), lo <<< 10⟩,
      ⟨(.reg (countHighReg v form) : Operand 64), Length.Shld.result hi lo⟩] ++
      (if form = .traitFinalizeIntoReset false then
        [⟨(.reg (if v = .sha512 then 13 else 5) : Operand 64), memLoad s.external (rspOf s + 240) 64⟩,
         ⟨(.reg (if v = .sha512 then 5 else 3) : Operand 64), rspOf s + 384⟩] else []) ++
      [⟨(.reg (countTailReg v form) : Operand 64), tail⟩,
       ⟨(.reg (countPadReg v form) : Operand 64), tail ^^^ 127⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

def countBytes (v : Variant) (form : Form) : List UInt8 :=
  match form with
  | .reset stage => if stage.val = 2 then [0x0f,0xb6,0x44,0x24,0x7f,0x4c,0x8b,0xb4,0x24,0xc0,0x00,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xc8,0x00,0x00,0x00,0x4d,0x0f,0xa4,0xf7,0x0a,0x49,0xc1,0xe6,0x0a,0xeb,0x08,0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x44,0x0f,0xb6,0xe0,0x4c,0x89,0xe3,0x48,0x83,0xf3,0x7f] else (if v = .sha512 then [0x0f,0xb6,0x44,0x24,0x7f,0x4c,0x8b,0xb4,0x24,0xc0,0x00,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xc8,0x00,0x00,0x00,0x4d,0x0f,0xa4,0xf7,0x0a,0x49,0xc1,0xe6,0x0a,0xeb,0x27,0x48,0x89,0x50,0x38,0x48,0x89,0x48,0x30,0x48,0x89,0x78,0x28,0x48,0x89,0x70,0x20,0x4c,0x89,0x48,0x18,0x4c,0x89,0x40,0x10,0x4c,0x89,0x58,0x08,0x4c,0x89,0x10,0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x0f,0xb6,0xe8,0x48,0x89,0xeb,0x48,0x83,0xf3,0x7f] else [0x0f,0xb6,0x44,0x24,0x7f,0x4c,0x8b,0xb4,0x24,0xc0,0x00,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xc8,0x00,0x00,0x00,0x4d,0x0f,0xa4,0xf7,0x0a,0x49,0xc1,0xe6,0x0a,0xeb,0x27,0x48,0x89,0x48,0x38,0x48,0x89,0x50,0x30,0x48,0x89,0x78,0x28,0x48,0x89,0x70,0x20,0x4c,0x89,0x48,0x18,0x4c,0x89,0x40,0x10,0x4c,0x89,0x58,0x08,0x4c,0x89,0x10,0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x0f,0xb6,0xe8,0x48,0x89,0xeb,0x48,0x83,0xf3,0x7f])
  | .finalizeIntoReset _ => if v = .sha384 ∨ v = .sha512 then [0x0f,0xb6,0x84,0x24,0x8f,0x00,0x00,0x00,0x4c,0x8b,0xb4,0x24,0xd0,0x00,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xd8,0x00,0x00,0x00,0x4d,0x0f,0xa4,0xf7,0x0a,0x49,0xc1,0xe6,0x0a,0x44,0x0f,0xb6,0xe8,0x4c,0x89,0xeb,0x48,0x83,0xf3,0x7f] else [0x0f,0xb6,0x84,0x24,0x8f,0x00,0x00,0x00,0x4c,0x8b,0xb4,0x24,0xd0,0x00,0x00,0x00,0x4c,0x8b,0xa4,0x24,0xd8,0x00,0x00,0x00,0x4d,0x0f,0xa4,0xf4,0x0a,0x49,0xc1,0xe6,0x0a,0x44,0x0f,0xb6,0xe8,0x4c,0x89,0xeb,0x48,0x83,0xf3,0x7f]
  | _ => if v = .sha512 then [0x0f,0xb6,0x84,0x24,0x7f,0x01,0x00,0x00,0x4c,0x8b,0xb4,0x24,0xc0,0x01,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xc8,0x01,0x00,0x00,0x4d,0x0f,0xa4,0xf7,0x0a,0x49,0xc1,0xe6,0x0a,0x4c,0x8b,0xac,0x24,0xf0,0x00,0x00,0x00,0xeb,0x08,0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x48,0x8d,0xac,0x24,0x80,0x01,0x00,0x00,0x44,0x0f,0xb6,0xe0,0x4c,0x89,0xe3,0x48,0x83,0xf3,0x7f] else [0x0f,0xb6,0x84,0x24,0x7f,0x01,0x00,0x00,0x4c,0x8b,0xbc,0x24,0xc0,0x01,0x00,0x00,0x4c,0x8b,0xa4,0x24,0xc8,0x01,0x00,0x00,0x4d,0x0f,0xa4,0xfc,0x0a,0x49,0xc1,0xe7,0x0a,0x48,0x8b,0xac,0x24,0xf0,0x00,0x00,0x00,0xeb,0x08,0x45,0x31,0xff,0x45,0x31,0xe4,0x31,0xc0,0x48,0x8d,0x9c,0x24,0x80,0x01,0x00,0x00,0x44,0x0f,0xb6,0xe8,0x4d,0x89,0xee,0x49,0x83,0xf6,0x7f]

theorem countCode {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    CodeIn (codeRange (v.pc (countStartOffset v form) form) (countBytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + countStartOffset v form) (countBytes v form)
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate Sha2.Proofs.Common.Instructions.ShiftLeft
attribute [local x86_compose] Length.Shld.effect shlR64Effect
attribute [local x86_local] Length.Machine.shld_local
  Sha2.Proofs.Wrapper.Hash.Padding.Length.shift64_local

macro "count_load_steps " kind:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let k := kind.getId.toString
  let reset := k == "reset1" || k == "reset2"
  let first := k == "reset1"
  let trait := k == "trait15" || k == "trait14"
  let lo := if k == "trait15" then 15 else 14
  let hi := if k == "trait15" || k == "final12" then 12 else 15
  let tr := if first then 5 else if k == "reset2" || k == "trait14" then 12 else 13
  let pr := if k == "trait15" then 14 else 3
  let tail := if reset then 127 else if trait then 383 else 143
  let loadLen := if reset then 5 else 8
  let shldPos := loadLen + 16
  let shlPos := shldPos + 5
  let afterShift := shlPos + 4
  let jumpPos := afterShift + if trait then 8 else 0
  let displacement := if first then 39 else 8
  let target := if reset || trait then jumpPos + 2 + displacement else afterShift
  let tailPos := target + if trait then 8 else 0
  let movePos := tailPos + if first then 3 else 4
  let xorPos := movePos + 3
  let size := xorPos + 4
  let tailDisp ← if reset then `(Disp.d8 127) else `(Disp.d32 $(Lean.quote tail))
  let restore ← if trait then `(tactic| (
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote afterShift))
      $(Lean.quote (if k == "trait14" then 0x4c else 0x48)) (by simp [RexWPrefix])
      5 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote jumpPos) (by decide)))
))
    else `(tactic| skip)
  let jump ← if reset || trait then `(tactic| (
    have low : (branchTarget ($pc + $(Lean.quote jumpPos)) 2
        (($(Lean.quote displacement) : BitVec 8).signExtend 64)).toNat < 2^32 := by
      obtain ⟨byte, mem⟩ := $inside $(Lean.quote target) (by decide)
      have bound := programSections_low.codeLow (_, byte) mem
      simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
    advance_reloc_then (jmp_rel8_effect_step ($pc + $(Lean.quote jumpPos)) $(Lean.quote displacement) low)
      next (boundary_ne_program $outside ($inside $(Lean.quote target) (by decide)))))
    else `(tactic| skip)
  let pointer ← if trait then `(tactic| (
    advance_reloc_then (lea_r64_effect_step ($pc + $(Lean.quote target)) 0x48
      (by simp [RexWPrefix]) $(Lean.quote (if k == "trait14" then 5 else 3))
      (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote tailPos) (by decide)))))
    else `(tactic| skip)
  let tailStep ← if first then `(movzx_r32_r8_effect_step ($pc + $(Lean.quote tailPos)) 0xe8 rfl (by decide))
    else `(movzx_r32_r8_rex_effect_step ($pc + $(Lean.quote tailPos)) 0x44 (by simp [RexNoWPrefix])
      $(Lean.quote (if tr == 12 then 0xe0 else 0xe8)) rfl)
  `(tactic| (
    advance_reloc_begin (movzx_r32_m8_effect_step $pc 0 (.sib 4 none 0 $tailDisp) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote loadLen) (by decide)))
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote loadLen)) 0x4c
      (by simp [RexWPrefix]) $(Lean.quote (lo-8)) (.sib 4 none 0 (.d32 $(Lean.quote (tail+65)))) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote (loadLen+8)) (by decide)))
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote (loadLen+8))) 0x4c
      (by simp [RexWPrefix]) $(Lean.quote (hi-8)) (.sib 4 none 0 (.d32 $(Lean.quote (tail+73)))) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote shldPos) (by decide)))
    advance_reloc_then (show StepEffect _ _ (Length.Shld.effect ($pc + $(Lean.quote shldPos)) $(Lean.quote hi) $(Lean.quote lo)) from
      Length.Shld.effect_step ($pc + $(Lean.quote shldPos)) 0x4d $(Lean.quote (192 + (lo-8)*8 + hi-8))
        (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote shlPos) (by decide)))
    advance_reloc_then (StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (shlR64Effect ($pc + $(Lean.quote shlPos)) 4 $(Lean.quote lo) 10) from
        shl_r64_imm8_effect_step ($pc + $(Lean.quote shlPos)) 0x49 $(Lean.quote (224+lo-8)) 10
          (by simp [RexWPrefix]) rfl rfl)))
      next (boundary_ne_program $outside ($inside $(Lean.quote afterShift) (by decide)))
    $restore:tactic
    $jump:tactic
    $pointer:tactic
    advance_reloc_then $tailStep
      next (boundary_ne_program $outside ($inside $(Lean.quote movePos) (by decide)))
    advance_reloc_then (mov_r64_r64_effect_step ($pc + $(Lean.quote movePos))
      $(Lean.quote (if tr == 5 then 0x48 else if pr == 14 then 0x4d else 0x4c))
      $(Lean.quote (192 + (tr%8)*8 + pr%8)) (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote xorPos) (by decide)))
    advance_reloc_then (StepEffect.forgetFlags (h :=
      xor_r64_imm8_effect_step ($pc + $(Lean.quote xorPos))
        $(Lean.quote (if pr == 14 then 0x49 else 0x48)) $(Lean.quote (240+pr%8)) 127
        (by simp [RexWPrefix]) rfl rfl))
      next (boundary_ne_program $outside ($inside $(Lean.quote size) (by decide)))
    advance_finish [countEffect, countLength, countTailOffset, countLowReg, countHighReg,
      countTailReg, countPadReg, countBytes, BitVec.setWidth_setWidth_of_le]
    ))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem run_count [Bindings] (v : Variant) (p : BitVec 64) (form : Form)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (countLength form))
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    AdvanceTriple boundary (fun s => CountPre p s form) (codeRange p (countBytes v form))
      (Effect.post (fun s => countEffect v p s form)) := by
  rcases eligible with rfl | rfl | rfl | rfl
  · cases v <;> count_load_steps reset1, p, outside, inside
  · cases v <;> count_load_steps reset2, p, outside, inside
  · cases v
    · count_load_steps final15, p, outside, inside
    · count_load_steps final15, p, outside, inside
    · count_load_steps final12, p, outside, inside
    · count_load_steps final12, p, outside, inside
  · cases v
    · count_load_steps trait15, p, outside, inside
    · count_load_steps trait14, p, outside, inside
    · count_load_steps trait15, p, outside, inside
    · count_load_steps trait15, p, outside, inside

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate

abbrev emptyTailStart (v : Variant) (form : Form) : Nat :=
  match form with
  | .reset stage => if stage.val = 2 then (match v with
      | .sha384 => 0x739 | .sha512 => 0x759 | _ => 0x719) else 0x3f4
  | .finalizeIntoReset _ => 0x22c
  | _ => 0x281
abbrev emptyTailLength (form : Form) : Nat :=
  match form with
  | .reset stage => if stage.val = 2 then 19 else 18
  | .finalizeIntoReset _ => 11
  | _ => 27

def emptyTailEffect (v : Variant) (p : BitVec 64) (s : RamState) (form : Form) : Effect :=
  let tail := if form = .finalizeIntoReset false then (s.regValue .rax).setWidth 8 |>.setWidth 64 else 0
  { rip := p + BitVec.ofNat 64 (emptyTailLength form)
    writes := (if form = .finalizeIntoReset false then [] else
      [⟨(.reg (countLowReg v form) : Operand 64), 0⟩,
       ⟨(.reg (countHighReg v form) : Operand 64), 0⟩,
       ⟨(.reg 0 : Operand 64), 0⟩]) ++
      (if form = .traitFinalizeIntoReset false then
        [⟨(.reg (if v = .sha512 then 5 else 3) : Operand 64), rspOf s + 384⟩] else []) ++
      [⟨(.reg (countTailReg v form) : Operand 64), tail⟩,
       ⟨(.reg (countPadReg v form) : Operand 64), tail ^^^ 127⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

def emptyTailBytes (v : Variant) (form : Form) : List UInt8 :=
  match form with
  | .reset stage => if stage.val = 2 then [0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x44,0x0f,0xb6,0xe0,0x4c,0x89,0xe3,0x48,0x83,0xf3,0x7f] else [0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x0f,0xb6,0xe8,0x48,0x89,0xeb,0x48,0x83,0xf3,0x7f]
  | .finalizeIntoReset _ => [0x44,0x0f,0xb6,0xe8,0x4c,0x89,0xeb,0x48,0x83,0xf3,0x7f]
  | _ => if v = .sha512 then [0x45,0x31,0xf6,0x45,0x31,0xff,0x31,0xc0,0x48,0x8d,0xac,0x24,0x80,0x01,0x00,0x00,0x44,0x0f,0xb6,0xe0,0x4c,0x89,0xe3,0x48,0x83,0xf3,0x7f] else [0x45,0x31,0xff,0x45,0x31,0xe4,0x31,0xc0,0x48,0x8d,0x9c,0x24,0x80,0x01,0x00,0x00,0x44,0x0f,0xb6,0xe8,0x4d,0x89,0xee,0x49,0x83,0xf6,0x7f]

theorem emptyTailCode {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    CodeIn (codeRange (v.pc (emptyTailStart v form) form) (emptyTailBytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + emptyTailStart v form) (emptyTailBytes v form)
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel
  · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate

macro "empty_tail_steps " kind:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let state := Lean.mkIdent `s
  let k := kind.getId.toString
  let first := k == "reset1"
  let final := k == "final"
  let trait := k == "trait15" || k == "trait14"
  let lo := if k == "trait15" then 15 else 14
  let hi := if k == "trait15" then 12 else 15
  let tr := if first then 5 else if k == "reset2" || k == "trait14" then 12 else 13
  let pr := if k == "trait15" then 14 else 3
  let tailPos := if final then 0 else if trait then 16 else 8
  let movePos := tailPos + if first then 3 else 4
  let xorPos := movePos + 3
  let size := xorPos + 4
  let tailStep ← if first then `(movzx_r32_r8_effect_step ($pc + $(Lean.quote tailPos)) 0xe8 rfl (by decide))
    else `(movzx_r32_r8_rex_effect_step ($pc + $(Lean.quote tailPos)) 0x44 (by simp [RexNoWPrefix])
      $(Lean.quote (if tr == 12 then 0xe0 else 0xe8)) rfl)
  let prefixTac ← if final then `(tactic| (
    advance_reloc_begin $tailStep
      next (boundary_ne_program $outside ($inside $(Lean.quote movePos) (by decide)))))
    else `(tactic| (
      advance_reloc_begin (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step $pc
        0x45 $(Lean.quote (192+(lo%8)*9)) (by simp [RexNoWPrefix]) rfl))
        next (boundary_ne_program $outside ($inside 3 (by decide)))
      advance_reloc_then (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step ($pc + 3)
        0x45 $(Lean.quote (192+(hi%8)*9)) (by simp [RexNoWPrefix]) rfl))
        next (boundary_ne_program $outside ($inside 6 (by decide)))
      advance_reloc_then (StepEffect.forgetFlags (h := xor_r32_r32_effect_step ($pc + 6) 0xc0 rfl))
        next (boundary_ne_program $outside ($inside 8 (by decide)))))
  let pointer ← if trait then `(tactic| (
    advance_reloc_then (lea_r64_effect_step ($pc + 8) 0x48 (by simp [RexWPrefix])
      $(Lean.quote (if k == "trait14" then 5 else 3)) (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside 16 (by decide)))))
    else `(tactic| skip)
  let tail ← if final then `(tactic| skip) else `(tactic| (
    advance_reloc_then $tailStep
      next (boundary_ne_program $outside ($inside $(Lean.quote movePos) (by decide)))))
  let writesTac ← if final then `(tactic| exact ⟨rfl, rfl⟩) else `(tactic| (
    change (0#64 = (((.reg $(Lean.quote lo) : Operand 32).read $state) ^^^ ((.reg $(Lean.quote lo) : Operand 32).read $state)).setWidth 64) ∧
      (0#64 = (((.reg $(Lean.quote hi) : Operand 32).read $state) ^^^ ((.reg $(Lean.quote hi) : Operand 32).read $state)).setWidth 64) ∧
      (0#64 = (((.reg 0 : Operand 32).read $state) ^^^ ((.reg 0 : Operand 32).read $state)).setWidth 64) ∧
      (0#64 = ((((.reg 0 : Operand 32).read $state) ^^^ ((.reg 0 : Operand 32).read $state)).setWidth 8).setWidth 64) ∧
      (127#64 = (((((.reg 0 : Operand 32).read $state) ^^^ ((.reg 0 : Operand 32).read $state)).setWidth 8).setWidth 64) ^^^ 127)
    simp))
  `(tactic| (
    $prefixTac:tactic
    $pointer:tactic
    $tail:tactic
    advance_reloc_then (mov_r64_r64_effect_step ($pc + $(Lean.quote movePos))
      $(Lean.quote (if tr == 5 then 0x48 else if pr == 14 then 0x4d else 0x4c))
      $(Lean.quote (192 + (tr%8)*8 + pr%8)) (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote xorPos) (by decide)))
    advance_reloc_then (StepEffect.forgetFlags (h :=
      xor_r64_imm8_effect_step ($pc + $(Lean.quote xorPos))
        $(Lean.quote (if pr == 14 then 0x49 else 0x48)) $(Lean.quote (240+pr%8)) 127
        (by simp [RexWPrefix]) rfl rfl))
      next (boundary_ne_program $outside ($inside $(Lean.quote size) (by decide)))
    apply AdvanceTriple.block_end
    intro $state t _ h
    apply h.weaken
    · x86_norm [emptyTailEffect, emptyTailLength, countLowReg, countHighReg, countTailReg, countPadReg]
    · x86_norm [emptyTailEffect, emptyTailLength, countLowReg, countHighReg, countTailReg, countPadReg]
      $writesTac:tactic
    · intro i; cases i <;> x86_norm [emptyTailEffect]
    · x86_norm [emptyTailEffect, countLowReg, countHighReg, countTailReg, countPadReg]))


set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem run_empty_tail [Bindings] (v : Variant) (p : BitVec 64) (form : Form)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (emptyTailLength form))
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (emptyTailBytes v form))
      (Effect.post (fun s => emptyTailEffect v p s form)) := by
  rcases eligible with rfl | rfl | rfl | rfl
  · cases v <;> empty_tail_steps reset1, p, outside, inside
  · cases v <;> empty_tail_steps reset2, p, outside, inside
  · cases v <;> empty_tail_steps final, p, outside, inside
  · cases v
    · empty_tail_steps trait15, p, outside, inside
    · empty_tail_steps trait14, p, outside, inside
    · empty_tail_steps trait15, p, outside, inside
    · empty_tail_steps trait15, p, outside, inside

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions

structure EmptyStorePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ i < 8, MemWritable s (s.regValue .rax + BitVec.ofNat 64 (8*i)) 8
  apart : ∀ i < 8, ∀ j n : Nat, j+n ≤ 31 →
    RangeApart (s.regValue .rax + BitVec.ofNat 64 (8*i)) 8 (p + BitVec.ofNat 64 j) n

def emptyStoreEffect (v : Variant) (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 31
    writes := [7,6,5,4,3,2,1,0].map fun i =>
      ⟨(.mem (s.regValue .rax + BitVec.ofNat 64 (8*i)) : Operand 64),
        (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s⟩ }

def emptyStoreBytes (v : Variant) : List UInt8 :=
  if v = .sha512 then [0x48,0x89,0x50,0x38,0x48,0x89,0x48,0x30,0x48,0x89,0x78,0x28,0x48,0x89,0x70,0x20,0x4c,0x89,0x48,0x18,0x4c,0x89,0x40,0x10,0x4c,0x89,0x58,0x08,0x4c,0x89,0x10] else [0x48,0x89,0x48,0x38,0x48,0x89,0x50,0x30,0x48,0x89,0x78,0x28,0x48,0x89,0x70,0x20,0x4c,0x89,0x48,0x18,0x4c,0x89,0x40,0x10,0x4c,0x89,0x58,0x08,0x4c,0x89,0x10]

theorem emptyStoreCode {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x3d5 (.reset 1)) (emptyStoreBytes v)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset (.reset 1) + 0x3d5) (emptyStoreBytes v)
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions

macro "empty_store_steps " swapped:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let swap := swapped.getId == `yes
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  for j in [:8] do
    let i := 7-j
    let reg := if i == 7 then (if swap then 2 else 1) else if i == 6 then (if swap then 1 else 2)
      else if i == 5 then 7 else if i == 4 then 6 else if i == 3 then 9
      else if i == 2 then 8 else if i == 1 then 11 else 10
    let len := if i == 0 then 3 else 4
    let off := 4*j
    let disp ← if i == 0 then `(Disp.none) else `(Disp.d8 $(Lean.quote (8*i)))
    let step ← `(mov_m64_r64_effect_step ($pc + $(Lean.quote off))
      $(Lean.quote (if reg < 8 then 0x48 else 0x4c)) (by simp [RexWPrefix])
      $(Lean.quote (reg%8)) (.base 0 $disp) (by decide) rfl rfl)
    let tac ← Lean.withFreshMacroScope do
      if j == 0 then `(tactic| (
      refine Sha2.Proofs.Common.Field.AdvanceTriple.block_first ?k $step ?sub ?pre ?av ?«next»
      case sub => x86_sub
      case pre =>
        intro s hp
        refine ⟨?_, ?_, ?_⟩
        · simpa using hp.rip
        · exact hp.writable $(Lean.quote i) (by decide)
        · exact hp.apart $(Lean.quote i) (by decide) $(Lean.quote off) $(Lean.quote len) (by decide)
      case av =>
        intro s hp
        apply Effect.avoids_codeRange
        x86_norm
        simpa [State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using hp.apart $(Lean.quote i) (by decide) 0 31 (by decide)
      case «next» =>
        intro s hp
        x86_norm
        exact boundary_ne_program $outside ($inside $(Lean.quote (off+len)) (by decide))
      case' k => x86_norm))
      else `(tactic| (
        refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid
        case loc => x86_local
        case sub => x86_sub
        case full => x86_full
        case mid =>
          intro s t hp hh ho
          refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
          · x86_norm
            simpa [State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using hp.writable $(Lean.quote i) (by decide)
          · x86_norm
            simpa [State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using hp.apart $(Lean.quote i) (by decide) $(Lean.quote off) $(Lean.quote len) (by decide)
          · apply Effect.Local.avoids (by x86_local) (ho true)
            apply Effect.avoids_codeRange
            x86_norm
            simpa [State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using hp.apart $(Lean.quote i) (by decide) 0 31 (by decide)
          · x86_norm
            exact boundary_ne_program $outside ($inside $(Lean.quote (off+len)) (by decide))
        case' k => x86_norm))
    steps := steps.push tac
  `(tactic| (
    $[$steps:tactic]*
    apply AdvanceTriple.block_end
    intro s t hp h
    refine Eq.mp ?_ h
    congr 1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem run_empty_store [Bindings] (v : Variant) (p : BitVec 64)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p 31) :
    AdvanceTriple boundary (fun s => EmptyStorePre p s) (codeRange p (emptyStoreBytes v))
      (Effect.post (emptyStoreEffect v p)) := by
  cases v
  · empty_store_steps no, p, outside, inside
  · empty_store_steps yes, p, outside, inside
  · empty_store_steps no, p, outside, inside
  · empty_store_steps no, p, outside, inside

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
