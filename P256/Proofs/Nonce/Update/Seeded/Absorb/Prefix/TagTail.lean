import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Nonce.Update.Prepare.CompressionSetup
import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagHead
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Instructions.Lea32
open P256.Proofs.Common.Instructions

attribute [local x86_compose] leaR32Effect movM8Imm8Effect incR32Effect Effect.forgetFlags
attribute [local x86_local] Prepare.CompressionSetup.byteStore_local TagHead.store_local

@[local x86_local] theorem inc_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (fun s => Effect.forgetFlags (incR32Effect p len dst s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Effect.forgetFlags, incR32Effect, h.read_reg]
  · intro s
    simp [Effect.forgetFlags, incR32Effect, Write.Full, Operand.Full]

@[local x86_local] theorem jmp_local (p : BitVec 64) (len : Nat) (disp : BitVec 64) :
    Effect.Local (fun _ : RamState => jmpEffect p len disp) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h; rfl
  · intro s; simp [jmpEffect]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a67d
  position : (Operand.reg 0#5 : Operand 64).read s = 32#64
  writable : ∀ off ∈ ([352,383] : List (BitVec 64)), MemWritable s (rspOf s + off) 1
  codeApart : ∀ off ∈ ([352,383] : List (BitVec 64)), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + off) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0xc6, 0x84, 0x4, 0x40, 0x1, 0x0, 0x0, 0x1, 0xff, 0xc0, 0x4c, 0x8d, 0xb4, 0x24, 0x80, 0x1, 0x0, 0x0, 0xe9, 0xad, 0x0, 0x0, 0x0, 0xba, 0x40, 0x0, 0x0, 0x0, 0x4c, 0x29, 0xfa, 0x48, 0x8b, 0x74, 0x24, 0x40, 0x48, 0x8d, 0x1c, 0x16, 0x4b, 0x8d, 0x3c, 0x3c, 0x49, 0x83, 0xc7, 0xe0, 0x4c, 0x8d, 0x35, 0x7c, 0x22, 0x1, 0x0, 0x41, 0xff, 0xd6, 0x48, 0xff, 0x84, 0x24, 0xa0, 0x1, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6, 0xe8, 0xc1, 0xb2, 0x0, 0x0, 0x4c, 0x89, 0xfe, 0x48, 0xb8, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x21, 0xc6, 0x48, 0x1, 0xde, 0x44, 0x88, 0xbc, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfa, 0x41, 0xff, 0xd6, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x41, 0xf, 0xb6, 0xc7, 0x3c, 0x3f, 0xf, 0x85, 0x75, 0xff, 0xff, 0xff, 0xba, 0x40, 0x0, 0x0, 0x0, 0x48, 0x29, 0xc2, 0x49, 0x8d, 0x3c, 0x4, 0xbe, 0x1, 0x0, 0x0, 0x0, 0xff, 0x15, 0x31, 0x9e, 0xf, 0x0, 0x48, 0xff, 0x84, 0x24, 0xa0, 0x1, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x8d, 0xb4, 0x24, 0x80, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xe6, 0xe8, 0x51, 0xb2, 0x0, 0x0, 0x31, 0xc0, 0x88, 0x84, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x4c, 0x8d, 0x2d, 0xe1, 0x21, 0x1, 0x0, 0xeb, 0x3c, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2e, 0xf, 0x1f, 0x84, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x89, 0xfe, 0x4c, 0x1, 0xe7, 0x48, 0x89, 0xda, 0x41, 0xff, 0xd5, 0x44, 0x0, 0xf3, 0x4c, 0x8d, 0xb4, 0x24, 0x80, 0x1, 0x0, 0x0, 0x88, 0x9c, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x48, 0x83, 0xc5, 0x10, 0x48, 0x3b, 0x6c, 0x24, 0x50, 0xf, 0x84, 0xbc, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a78d
    writes := [⟨(.mem (rspOf s + 352) : Operand 8),1⟩,
      ⟨(.reg 0 : Operand 64),33⟩,
      ⟨(.reg 14 : Operand 64),rspOf s + 384⟩,
      ⟨(.mem (rspOf s + 383) : Operand 8),33⟩,
      ⟨(.reg 13 : Operand 64),0x11c930⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a67d bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa67d bytes
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a67d bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10a67d (.sib 4 (some 0) 0 (.d32 320))
    (by decide +kernel) rfl rfl 1)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_, ?_⟩
    · x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.writable 352 (by simp)
    · x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.codeApart 352 (by simp) 0xa67d 8 (by decide)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    simp only [movM8Imm8Effect, storeEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl
    · cases eq
      x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.codeApart 352 (by simp) 0xa67d 272 (by decide)
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa685 (by decide))
  advance_then (StepEffect.forgetFlags (inc_r32_effect_step 0x10a685 0xc0 rfl rfl))
  case sub => exact codeRange_slice_subset 0x10a67d bytes 8 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, Effect.forgetFlags, incR32Effect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa687 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10a687 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a67d bytes 10 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa68f (by decide))⟩
  advance_then (jmp_rel32_effect_step 0x10a68f 0xad (by decide))
  case sub => exact codeRange_slice_subset 0x10a67d bytes 18 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, jmpEffect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa741 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.mov_m8_r8_legacy_effect_step 0x10a741 0 (by decide) (.sib 4 none 0 (.d32 383))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a67d bytes 196 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 383 (by simp)
    · x86_norm
      exact hP.codeApart 383 (by simp) 0xa741 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 383 (by simp) 0xa67d 272 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa748 (by decide))
  advance_then (lea_r64_effect_step 0x10a748 0x4c (by simp [RexWPrefix]) 5 (.rip 0x121e1) trivial rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a67d bytes 203 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa74f (by decide))⟩
  advance_then (jmp_rel8_effect_step 0x10a74f 0x3c (by decide))
  case sub => exact codeRange_slice_subset 0x10a67d bytes 210 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, jmpEffect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa78d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, hP.position, show gprNumber (0#1) (0#1) (modrmRm 192) = 0#5 from rfl, incR32Effect, Effect.forgetFlags, jmpEffect, show ((Operand.reg 0#5 : Operand 32).read s) = 32#32 from by change ((Operand.reg 0#5 : Operand 64).read s).setWidth 32 = _; rw [hP.position]; rfl]
  · x86_norm [effect, hP.position, show gprNumber (0#1) (0#1) (modrmRm 192) = 0#5 from rfl, incR32Effect, Effect.forgetFlags, jmpEffect, show ((Operand.reg 0#5 : Operand 32).read s) = 32#32 from by change ((Operand.reg 0#5 : Operand 64).read s).setWidth 32 = _; rw [hP.position]; rfl]
  · intro i; cases i <;> x86_norm [effect, hP.position, show gprNumber (0#1) (0#1) (modrmRm 192) = 0#5 from rfl, incR32Effect, Effect.forgetFlags, jmpEffect, show ((Operand.reg 0#5 : Operand 32).read s) = 32#32 from by change ((Operand.reg 0#5 : Operand 64).read s).setWidth 32 = _; rw [hP.position]; rfl]
  · x86_norm [effect, hP.position, show gprNumber (0#1) (0#1) (modrmRm 192) = 0#5 from rfl, incR32Effect, Effect.forgetFlags, jmpEffect, show ((Operand.reg 0#5 : Operand 32).read s) = 32#32 from by change ((Operand.reg 0#5 : Operand 64).read s).setWidth 32 = _; rw [hP.position]; rfl]

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagTail
