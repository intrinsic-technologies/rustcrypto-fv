import Hkdf.Proofs.Common.Machine
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return.Stores

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field
open Hkdf.Proofs.Common.Instructions.CrossPageStore

attribute [local x86_compose] gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10e240
  readable : ∀ i ∈ ([216,224,232,240] : List (BitVec 64)), MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), Writable s ((Operand.reg 3 : Operand 64).read s + i) 8
  byteWritable : MemWritable s ((Operand.reg 3 : Operand 64).read s + 95) 1
  codeApart : ∀ i ∈ ([0,8,16,24,95] : List (BitVec 64)),
    ∀ offset len : Nat, 0x10e240 ≤ offset → offset + len ≤ 0x10e273 →
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) (if i = 95 then 1 else 8) (BitVec.ofNat 64 offset) len
  apart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    ∀ j ∈ ([216,224,232,240] : List (BitVec 64)),
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8 (rspOf s + j) 8

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0xf0,0,0,0,0x48,0x89,0x43,0x18,
   0x48,0x8b,0x84,0x24,0xe8,0,0,0,0x48,0x89,0x43,0x10,
   0x48,0x8b,0x84,0x24,0xd8,0,0,0,0x48,0x8b,0x8c,0x24,0xe0,0,0,0,
   0x48,0x89,0x4b,0x08,0x48,0x89,0x03,0xc6,0x43,0x5f,0]

def effect (s : RamState) : Effect :=
  { rip := 0x10e273
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 216) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 224) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24) : Operand 64), memLoad s.external (rspOf s + 240) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16) : Operand 64), memLoad s.external (rspOf s + 232) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8) : Operand 64), memLoad s.external (rspOf s + 224) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s) : Operand 64), memLoad s.external (rspOf s + 216) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 95) : Operand 8), 0⟩] }

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x10e240 ≤ ip → ip ≤ 0x10e273 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10e240 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10e240 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 240 (by simp)⟩
  case next => intro s h; exact outside 0x10e248 (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step_any 0x10e248 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 8 4
  case mid =>
    intro s t hp hh ho
    refine ⟨storePre_of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 24 (by simp)
    · x86_norm
      exact hp.codeApart 24 (by simp) 0x10e248 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 24 (by simp) 0x10e240 51 (by decide) (by decide)
    · exact outside 0x10e24c (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10e24c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 12 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 232 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e254 (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step_any 0x10e254 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 20 4
  case mid =>
    intro s t hp hh ho
    refine ⟨storePre_of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 16 (by simp)
    · x86_norm
      exact hp.codeApart 16 (by simp) 0x10e254 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 16 (by simp) 0x10e240 51 (by decide) (by decide)
    · exact outside 0x10e258 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10e258 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 24 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 216 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e260 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10e260 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 32 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 224 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e268 (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step_any 0x10e268 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 40 4
  case mid =>
    intro s t hp hh ho
    refine ⟨storePre_of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 8 (by simp)
    · x86_norm
      exact hp.codeApart 8 (by simp) 0x10e268 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 8 (by simp) 0x10e240 51 (by decide) (by decide)
    · exact outside 0x10e26c (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step_any 0x10e26c 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 44 3
  case mid =>
    intro s t hp hh ho
    refine ⟨storePre_of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 0 (by simp)
    · x86_norm
      exact hp.codeApart 0 (by simp) 0x10e26c 3 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 0 (by simp) 0x10e240 51 (by decide) (by decide)
    · exact outside 0x10e26f (by decide) (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10e26f (.base 3 (.d8 95)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e240 bytes 47 4
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.byteWritable
    · x86_norm
      exact hp.codeApart 95 (by simp) 0x10e26f 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 95 (by simp) 0x10e240 51 (by decide) (by decide)
    · exact outside 0x10e273 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hp hh
  have unchanged (m : Ram) (i : BitVec 64) (hi : i ∈ ([0,8,16,24] : List (BitVec 64)))
      (j : BitVec 64) (hj : j ∈ ([216,224,232,240] : List (BitVec 64))) (v : BitVec 64) :
      memLoad (memStore m ((Operand.reg 3 : Operand 64).read s + i) v) ((Operand.reg 4 : Operand 64).read s + j) 64 =
        memLoad m ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (hp.apart i hi j hj)
  have read24_232 (m : Ram) (v : BitVec 64) := unchanged m 24 (by decide) 232 (by decide) v
  have read24_216 (m : Ram) (v : BitVec 64) := unchanged m 24 (by decide) 216 (by decide) v
  have read16_216 (m : Ram) (v : BitVec 64) := unchanged m 16 (by decide) 216 (by decide) v
  have read24_224 (m : Ram) (v : BitVec 64) := unchanged m 24 (by decide) 224 (by decide) v
  have read16_224 (m : Ram) (v : BitVec 64) := unchanged m 16 (by decide) 224 (by decide) v
  x86_norm at read24_232 read24_216 read16_216 read24_224 read16_224
  have extReg (u : RamState) (r : BitVec 5) (v : BitVec 64) :
      ((Operand.reg r : Operand 64).write u v).external = u.external := rfl
  have extMem (u : RamState) (a : BitVec 64) (v : BitVec 64) :
      ((Operand.mem a : Operand 64).write u v).external = memStore u.external a v := rfl
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect, extReg, extMem, rexR, UInt8.toBitVec, BitVec.add_zero]
    simp only [read24_232, read24_216, read16_216, read24_224, read16_224,
      memLoad_external, true_or, or_true, true_and]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, rexR, UInt8.toBitVec, BitVec.add_zero]

end Hkdf.Proofs.Standard.Finalize.Suffix.Return.Stores
