import P256.Proofs.Generate.Sampler.Setup

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.SignatureFromDer.Parser.ReadSlice

structure ReadSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x100ca0
  writable : ∀ off ∈ ([0,8] : List (BitVec 64)),
    P256.Proofs.Common.Der.Memory.MemWritable s ((Operand.reg 14#5 : Operand 64).read s + off) 8
  apart : RangeApart ((Operand.reg 14#5 : Operand 64).read s) 16 0x100ca0#64 11

def readSetupBytes : List UInt8 :=
  [0x49,0x8d,0x5d,0xe0,0x49,0x89,0x2e,0x49,0x89,0x5e,0x8]

def readSetupEffect (s : RamState) : Effect :=
  { rip := 0x100cab
    writes := [⟨(.reg 3 : Operand 64), (Operand.reg 13#5 : Operand 64).read s - 32⟩,
      ⟨(.mem ((Operand.reg 14#5 : Operand 64).read s) : Operand 64), (Operand.reg 5#5 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 14#5 : Operand 64).read s+8) : Operand 64), (Operand.reg 13#5 : Operand 64).read s - 32⟩] }

theorem read_setup_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100ca0 readSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xca0 _ (by decide) (by decide +kernel)

theorem read_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ReadSetupPre (codeRange 0x100ca0 readSetupBytes) readSetupEffect := by
  have next (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  have h2 := next 0xca7 (by decide)
  have h3 := next 0xcab (by decide)
  advance_begin (lea_r64_effect_step 0x100ca0 0x49 (by simp [RexWPrefix]) 3
    (.base 13 (.d8 224)) (by decide) rfl rfl)
  case next => intro _ _; exact next 0xca4 (by decide)
  advance_then (P256.Proofs.Common.Der.Memory.mov_m64_r64_effect_step 0x100ca4 0x49
    (by simp [RexWPrefix]) 5 (.base 14 .none) (by decide) rfl rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Der.Memory.StorePre.of_holds hh (ho true) (by x86_norm)
      (by x86_addr_obs) ?_ ?_, ?_, h2⟩
    · x86_norm
      simpa only [BitVec.add_zero] using hp.writable 0#64 (by simp)
    · x86_norm
      intro i hi j hj eq
      apply hp.apart i (by omega) (4+j) (by omega)
      simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using eq
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj eq
      apply hp.apart i (by omega) j hj
      simpa only [BitVec.add_zero] using eq
  advance_then (P256.Proofs.Common.Der.Memory.mov_m64_r64_effect_step 0x100ca7 0x49
    (by simp [RexWPrefix]) 3 (.base 14 (.d8 8)) (by decide) rfl rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Der.Memory.StorePre.of_holds hh (ho true) (by x86_norm)
      (by x86_addr_obs) ?_ ?_, ?_, h3⟩
    · x86_norm
      exact hp.writable 8#64 (by simp)
    · x86_norm
      intro i hi j hj eq
      apply hp.apart (8+i) (by omega) (7+j) (by omega)
      simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using eq
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj eq
      apply hp.apart (8+i) (by omega) j hj
      simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using eq
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [readSetupEffect]
  · x86_norm [readSetupEffect,BitVec.sub_eq_add_neg]
    simp [Operand.read]
    all_goals rfl
  · intro i; cases i <;> x86_norm [readSetupEffect]
  · x86_norm [readSetupEffect]
    simp [Operand.read]
    all_goals rfl
  all_goals first
    | (simp only [BitVec.add_zero]; simp [Operand.read])
    | exact codeRange_slice_subset 0x100ca0 readSetupBytes 4 3
    | exact codeRange_slice_subset 0x100ca0 readSetupBytes 7 4

end P256.Proofs.Generate.Sampler
