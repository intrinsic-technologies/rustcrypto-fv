import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure OutputCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x114204
  readable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  tagWritable : MemWritable s ((Operand.reg 3 : Operand 64).read s+32) 1
  tagCode : ∀ offset len : Nat, offset+len≤118431 →
    RangeApart ((Operand.reg 3 : Operand 64).read s+32) 1
      (Extracted.textAddress+BitVec.ofNat 64 offset) len
  sourceApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ j ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      ((Operand.reg 4 : Operand 64).read s + j) 8

def outputCopyBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x43,0x18,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0x43,0x10,0x48,0x8b,0x4,0x24,0x48,0x8b,0x4c,0x24,0x8,0x48,0x89,0x4b,0x8,0x48,0x89,0x3,0x40,0x88,0x6b,0x20,0x48,0x89,0xd8]

def outputCopyEffect (s : RamState) : Effect :=
  { rip := 0x11422d
    writes := [
      ⟨(.reg 0 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 0) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32) : Operand 8),
        (Operand.reg 5 : Operand 8).read s⟩] }

theorem output_copy_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x114204 outputCopyBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x14204 outputCopyBytes
    (by decide +kernel) (by decide +kernel)

@[x86_local] theorem output_tag_store_local : Effect.Local
    (storeEffect 0x114226 4 (storeAddrAt 0x114226 (.base 3 (.d8 32)) 4)
      (fun s => (Operand.reg 5 : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

set_option maxHeartbeats 1600000 in
theorem output_copy [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputCopyPre (codeRange 0x114204 outputCopyBytes)
      (Effect.post outputCopyEffect) := by
  have er5 : gprNumber 0#1 (rexR (UInt8.toBitVec 0x40)) 5#3 = 5#5 := by decide +kernel
  have er3 : gprNumber 0#1 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xd8) = 3#5 := by decide +kernel
  advance_begin (mov_r64_m64_effect_step 0x114204 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 24 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14209 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x114209 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x14209 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x14204 41 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1420d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11420d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14212 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x114212 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x14212 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x14204 41 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14216 (by decide))
  advance_then (mov_r64_m64_effect_step 0x114216 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1421a (by decide))
  advance_then (mov_r64_m64_effect_step 0x11421a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 22 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1421f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11421f 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 27 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x1421f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x14204 41 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14223 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x114223 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 31 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x14223 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x14204 41 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14226 (by decide))
  advance_then (mov_m8_r8_effect_step 0x114226 0x40 (by simp [RexPrefix]) 5
    (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case loc => exact output_tag_store_local
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 34 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.tagWritable
    · x86_norm
      exact hP.tagCode 0x14226 4 (by decide)
    · apply Effect.Local.avoids output_tag_store_local (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.tagCode 0x14204 41 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1422a (by decide))
  advance_then (mov_r64_r64_effect_step 0x11422a 0x48 0xd8 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x114204 outputCopyBytes 38 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1422d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0, 8, 16, 24] : List (BitVec 64)))
      (hj : j ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + i) v)
        ((Operand.reg 4 : Operand 64).read s + j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart _ _ _ _ 64 (hP.sourceApart i hi j hj)
  have h2416 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h240 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h248 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h160 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h168 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h2416 h240 h248 h160 h168
  apply hH.weaken
  · x86_norm [outputCopyEffect]
  · x86_norm [outputCopyEffect, er5, er3, operand_write_reg_external, operand_write_mem_external, h2416, h240, h248, h160, h168]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [outputCopyEffect]
  · x86_norm [outputCopyEffect]

end P256.Proofs.Field.Inverse
