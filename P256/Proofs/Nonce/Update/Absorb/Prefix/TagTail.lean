import P256.Proofs.Nonce.Update.Prepare.CompressionSetup
import P256.Proofs.Nonce.Update.Absorb.Prefix.TagHead
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Instructions.Lea32

attribute [local x86_compose] leaR32Effect movM8Imm8Effect
attribute [local x86_local] Prepare.CompressionSetup.byteStore_local TagHead.store_local

@[local x86_local] theorem lea_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (len : Nat) :
    Effect.Local (leaR32Effect p dst am len) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [leaR32Effect, AddrMode.addr_obs h]
  · intro s
    simp [leaR32Effect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a196
  position : (Operand.reg 0#5 : Operand 64).read s = 32#64
  writable : ∀ off ∈ ([184,215] : List (BitVec 64)), MemWritable s (rspOf s + off) 1
  codeApart : ∀ off ∈ ([184,215] : List (BitVec 64)), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + off) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0xc6, 0x84, 0x4, 0x98, 0x0, 0x0, 0x0, 0x0, 0x8d, 0x58, 0x1, 0xe9, 0xb4, 0x0, 0x0, 0x0, 0xba, 0x40, 0x0, 0x0, 0x0, 0x4c, 0x29, 0xfa, 0x48, 0x8d, 0x1c, 0x16, 0x4b, 0x8d, 0x3c, 0x3e, 0x49, 0x83, 0xc7, 0xe0, 0x4c, 0x8d, 0x35, 0x6f, 0x27, 0x1, 0x0, 0x41, 0xff, 0xd6, 0x48, 0xff, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x48, 0x8d, 0xb4, 0x24, 0x98, 0x0, 0x0, 0x0, 0xe8, 0xaf, 0xb7, 0x0, 0x0, 0x4c, 0x89, 0xfe, 0x48, 0xb8, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x21, 0xc6, 0x48, 0x1, 0xde, 0x44, 0x88, 0xbc, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0x98, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xfa, 0x41, 0xff, 0xd6, 0x4c, 0x8d, 0xb4, 0x24, 0x98, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x41, 0xf, 0xb6, 0xc7, 0x3c, 0x3f, 0xf, 0x85, 0x6f, 0xff, 0xff, 0xff, 0xba, 0x40, 0x0, 0x0, 0x0, 0x48, 0x29, 0xc2, 0x49, 0x8d, 0x3c, 0x6, 0x31, 0xdb, 0x31, 0xf6, 0xff, 0x15, 0x13, 0xa3, 0xf, 0x0, 0x48, 0xff, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6, 0xe8, 0x36, 0xb7, 0x0, 0x0, 0x88, 0x9c, 0x24, 0xd7, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a261
    writes := [⟨(.mem (rspOf s + 184) : Operand 8),0⟩,
      ⟨(.reg 3 : Operand 64),33⟩,
      ⟨(.mem (rspOf s + 215) : Operand 8),33⟩] }

set_option maxRecDepth 1024 in
theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a196 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa196 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a196 bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10a196 (.sib 4 (some 0) 0 (.d32 152))
    (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_, ?_⟩
    · x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.writable 184 (by simp)
    · x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.codeApart 184 (by simp) 0xa196 8 (by decide)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    simp only [movM8Imm8Effect, storeEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl
    · cases eq
      x86_norm [hP.position, BitVec.shiftLeft_zero]
      exact hP.codeApart 184 (by simp) 0xa196 203 (by decide)
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa19e (by decide))
  advance_then (lea_r32_legacy_effect_step 0x10a19e 3 (.base 0 (.d8 1)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a196 bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, leaR32Effect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa1a1 (by decide))⟩
  advance_then (jmp_rel32_effect_step 0x10a1a1 0xb4 (by decide))
  case sub => exact codeRange_slice_subset 0x10a196 bytes 11 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, jmpEffect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa25a (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.mov_m8_r8_legacy_effect_step 0x10a25a 3 (by decide) (.sib 4 none 0 (.d32 215))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a196 bytes 196 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 215 (by simp)
    · x86_norm
      exact hP.codeApart 215 (by simp) 0xa25a 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 215 (by simp) 0xa196 203 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa261 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, hP.position]
  · x86_norm [effect, hP.position]
  · intro i; cases i <;> x86_norm [effect, hP.position]
  · x86_norm [effect, hP.position]

end P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
