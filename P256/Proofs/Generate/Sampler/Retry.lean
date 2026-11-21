import P256.Proofs.Generate.Sampler.Setup
import P256.Proofs.Common.Der.Decode.Header.Control
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import P256.Proofs.Common.Refine.Lemma.Norm

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.SignatureFromDer.Parser.ReadSlice

def retryBytes : List UInt8 :=
  [0x48,0x83,0xc5,0x20,0x49,0x89,0xdd,0x48,0x83,0xfb,0x20,0x73,0xae]

def retryEffect (s : RamState) : Effect :=
  { rip := 0x100ca0
    writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 32⟩,
      ⟨(.reg 13 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 3 : Operand 64).read s) 32)) }

theorem retry_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100ce5 retryBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xce5 _ (by decide) (by decide +kernel)

theorem retry_run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s => s.RIP = 0x100ce5 ∧ 32 ≤ ((Operand.reg 3 : Operand 64).read s).toNat)
      (codeRange 0x100ce5 retryBytes) retryEffect := by
  have next (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  advance_begin (add_r64_imm8_effect_step 0x100ce5 0x48 0xc5 32 (by simp [RexWPrefix]) rfl rfl)
  case next => intro _ _; exact next 0xce9 (by decide)
  advance_then (mov_r64_r64_effect_step 0x100ce9 0x49 0xdd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100ce5 retryBytes 4 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      next 0xcec (by decide)⟩
  advance_then (cmp_r64_imm8_effect_step 0x100cec 0x48 0xfb 32 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100ce5 retryBytes 7 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      next 0xcf0 (by decide)⟩
  advance_then (P256.Proofs.Common.Der.Decode.Header.jcc_rel8_taken_effect_step 0x100cf0 3 174
    (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x100ce5 retryBytes 11 2
  case mid =>
    intro s t hp hh ho
    refine ⟨⟨hh.rip_of (by x86_norm),?_⟩,
      Effect.Avoids.of_noMem (by simp [jmpEffect,Effect.components,Component.Covers]) _,
      next 0xca0 (by decide)⟩
    have carry := hh.flag .CF
    x86_norm at carry
    change (StatusFlags.ofRFLAGS t.RFLAGS).CF =
      (cmpSpec ((Operand.reg 3#5 : Operand 64).read s) 32#64).CF at carry
    change (!(StatusFlags.ofRFLAGS t.RFLAGS).CF) = true
    rw [carry,P256.Proofs.Refine.cmpSpec_CF]
    have low : ¬ ((Operand.reg 3#5 : Operand 64).read s) < 32#64 := by
      change ¬ ((Operand.reg 3#5 : Operand 64).read s).toNat < 32
      omega
    exact congrArg Bool.not (decide_eq_false low)
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [retryEffect]
  · x86_norm [retryEffect]
    exact ⟨rfl,rfl⟩
  · intro flag; cases flag <;> x86_norm [retryEffect] <;> rfl
  · x86_norm [retryEffect]

end P256.Proofs.Generate.Sampler
