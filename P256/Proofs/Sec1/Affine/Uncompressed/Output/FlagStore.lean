import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure FlagStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x110c64
  writable : ∀ i ∈ ([80,88] : List Nat), MemWritable s (stackPtr s+BitVec.ofNat 64 i) 1
  codeApart : ∀ i ∈ ([80,88] : List Nat), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+BitVec.ofNat 64 i) 1
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def flagStoreBytes : List UInt8 := [0xc6,0x44,0x24,0x50,0,0x88,0x44,0x24,0x58]

def flagStoreEffect (s : RamState) : Effect :=
  { rip := 0x110c6d
    writes := [⟨(.mem (stackPtr s+80) : Operand 8),0⟩,
      ⟨(.mem (stackPtr s+88) : Operand 8),(Operand.reg 0 : Operand 8).read s⟩] }

@[x86_local] theorem legacy_flag_store_local : Effect.Local
    (storeEffect 0x110c69 4 (storeAddrAt 0x110c69 (.sib 4 none 0 (.d8 88)) 4)
      (fun s => (Operand.reg 0 : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

theorem flag_store [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FlagStorePre (codeRange 0x110c64 flagStoreBytes)
      (Effect.post flagStoreEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x110c64 (.sib 4 none 0 (.d8 80))
    (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 80 (by simp),h.codeApart 80 (by simp) 0x10c64 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 80 (by simp) 0x10c64 9 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10c69 (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x110c69 0 (by decide)
    (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case loc => exact legacy_flag_store_local
  case sub => exact codeRange_slice_subset 0x110c64 flagStoreBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      exact hP.codeApart 88 (by simp) 0x10c69 4 (by decide)
    · apply Effect.Local.avoids legacy_flag_store_local (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 (by simp) 0x10c64 9 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c6d (by decide))
  advance_finish [flagStoreEffect, stackPtr, Operand.read_reg64, X86.State.regValue]

structure ResultStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x110d1a
  writable : ∀ i ∈ ([64,72] : List (BitVec 64)), MemWritable s ((Operand.reg 3 : Operand 64).read s+i) 1
  codeApart : ∀ i ∈ ([64,72] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s+i) 1
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def resultStoreBytes : List UInt8 := [0x44,0x88,0x7b,0x40,0x40,0x88,0x6b,0x48]

def resultStoreEffect (s : RamState) : Effect :=
  { rip := 0x110d22
    writes := [⟨(.mem ((Operand.reg 3 : Operand 64).read s+64) : Operand 8),(Operand.reg 15 : Operand 8).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s+72) : Operand 8),(Operand.reg 5 : Operand 8).read s⟩] }

@[x86_local] theorem byte_store_local (p : BitVec 64) (r : BitVec 5) (offset : BitVec 8) :
    Effect.Local (storeEffect p 4 (storeAddrAt p (.base 3 (.d8 offset)) 4)
      (fun s => (Operand.reg r : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

theorem result_store [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ResultStorePre (codeRange 0x110d1a resultStoreBytes)
      (Effect.post resultStoreEffect) := by
  advance_begin (mov_m8_r8_effect_step 0x110d1a 0x44 (by simp [RexPrefix]) 7
    (.base 3 (.d8 64)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 64 (by simp),h.codeApart 64 (by simp) 0x10d1a 4 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 64 (by simp) 0x10d1a 8 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10d1e (by decide))
  advance_then (mov_m8_r8_effect_step 0x110d1e 0x40 (by simp [RexPrefix]) 5
    (.base 3 (.d8 72)) (by decide) rfl rfl)
  case loc => exact byte_store_local _ _ _
  case sub => exact codeRange_slice_subset 0x110d1a resultStoreBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.codeApart 72 (by simp) 0x10d1e 4 (by decide)
    · apply Effect.Local.avoids (byte_store_local _ _ _) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp) 0x10d1a 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10d22 (by decide))
  advance_finish [resultStoreEffect,
    gprNumber, rexR, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
