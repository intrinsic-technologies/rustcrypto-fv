import P256.Proofs.Sec1.Decompress.Input.Load
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InputStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x10fc30
  writable : ∀ i ∈ ([80, 88, 96, 104] : List (BitVec 64)),
    MemWritable s (stackPtr s + i) 8
  codeApart : ∀ i ∈ ([80, 88, 96, 104] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 →
      RangeApart (stackPtr s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def inputStoreBytes : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x50, 0x4c, 0x89, 0x44, 0x24, 0x58,
    0x48, 0x89, 0x4c, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x68]

def inputStoreEffect (s : RamState) : Effect :=
  { rip := 0x10fc44
    writes := [
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 80) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 88) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 96) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem input_store_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InputStorePre (codeRange 0x10fc30 inputStoreBytes)
      (Effect.post inputStoreEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fc30 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 80 (by simp), hP.codeApart 80 (by simp) 0xfc30 5 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 80 (by simp) 0xfc30 20 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc35 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc35 0x4c (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc30 inputStoreBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      exact hP.codeApart 88 (by simp) 0xfc35 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 (by simp) 0xfc30 20 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc3a (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc3a 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc30 inputStoreBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 96 (by simp)
    · x86_norm
      exact hP.codeApart 96 (by simp) 0xfc3a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 96 (by simp) 0xfc30 20 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc3f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc3f 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc30 inputStoreBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 (by simp)
    · x86_norm
      exact hP.codeApart 104 (by simp) 0xfc3f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 (by simp) 0xfc30 20 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc44 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  exact hH

end P256.Proofs.Sec1.Decompress.Input
