import Sha2.Proofs.Reset.TraitFinalizeIntoReset
import Sha2.Proofs.Wrapper512.State
import Sha2.Proofs.Wrapper512.ResetLayout
import Sha2.Proofs.Reset.Dispatch
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxHeartbeats 1000000 in
theorem branch [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = v.pc 0xd0)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rsi = 0 then v.pc 0x218 else v.pc 0xd9) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, run, readyU, tested⟩ :=
    (test_r64_r64_effect_step (v.pc 0xd0) 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xd0)
        [0x48,0x85,0xf6] (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (boundary_ne_program outside (by
        have h := inProgram_of_textOffset (v.textOffset + 0xd3) (by cases v <;> decide)
        have h' : InProgram (v.pc 0xd0 + BitVec.ofNat 64 3) := by
          rw [Variant.pc_add]
          exact h
        simpa [testR64R64Effect, gprNumber, rexB, modrmRm, rexR, modrmReg] using h'))
  have frame : AgreesExcept [.flags,.rip] s u := tested.agrees
  have testedRip0 : u.RIP = v.pc 0xd0 + BitVec.ofNat 64 3 := by
    simpa [testR64R64Effect, gprNumber, rexB, modrmRm, rexR, modrmReg] using tested.rip
  have testedRip : u.RIP = v.pc 0xd3 := by
    rw [Variant.pc_add] at testedRip0
    exact testedRip0
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step (v.pc 0xd3) 4 0x13f u readyU
    (programText_slice
      (frame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      (v.textOffset + 0xd3) [0x0f,0x84,0x3f,0x01,0x00,0x00]
      (by cases v <;> decide) (by cases v <;> decide +kernel))
    ⟨testedRip, fun _ => by cases v <;> decide⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi == 0) := by
    have zero := tested.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi &&& s.regValue .rsi == 0) at zero
    simpa only [BitVec.and_self] using zero
  have target : t.RIP = (if s.regValue .rsi = 0 then v.pc 0x218 else v.pc 0xd9) := by
    rw [jumped.rip]
    simp only [jccEffect, branchEffect, branchTarget, condHolds]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then
      (v.pc 0xd3 + BitVec.ofNat 64 6 + BitVec.signExtend 64 (BitVec.ofNat 32 0x13f))
      else v.pc 0xd3 + BitVec.ofNat 64 6) = _
    rw [zero]
    simp only [beq_iff_eq]
    have hnext : v.pc 0xd3 + BitVec.ofNat 64 6 = v.pc 0xd9 := by
      exact Variant.pc_add v 0xd3 6
    have hoff : BitVec.signExtend 64 (BitVec.ofNat 32 0x13f) = BitVec.ofNat 64 0x13f := by
      decide +kernel
    rw [hoff, hnext]
    split
    · rw [Variant.pc_add v 0xd9 0x13f]
    · rfl
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (by
        apply Variant.pc_inProgram
        cases v <;> decide)
    · exact boundary_ne_program outside (by
        apply Variant.pc_inProgram
        cases v <;> decide)
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])⟩

def resetBranchSites : Variant → List (Nat × BitVec 4 × BitVec 32)
  | .sha384 => [(0x47d9, 12, 0x2e3), (0x4cf5, 12, 0x12b),
      (0x43b8, 12, 0x119), (0x509b, 6, 0x19d)]
  | .sha512 => [(0xa469, 12, 0x2e3), (0xa9a3, 12, 0x12d),
      (0xa026, 12, 0x11b), (0xad6b, 6, 0x19d)]
  | .sha512_224 => [(0x66a9, 12, 0x2e3), (0x6ba6, 12, 0x12a),
      (0x62a9, 15, 0x11a), (0x6f3b, 6, 0x19d)]
  | .sha512_256 => [(0x8509, 12, 0x2e3), (0x8a07, 12, 0x129),
      (0x810a, 15, 0x119), (0x8d9b, 6, 0x19d)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem resetBranchSites_valid (v : Variant) :
    ∀ site ∈ resetBranchSites v,
      site.1 + 9 < Extracted.textBytes.size ∧
      Extracted.textBytes.toListFrom site.1 9 =
        Sha2.Proofs.Reset.Dispatch.branchBytes site.2.2 site.2.1 ∧
      site.1 + 9 + site.2.2.toNat < Extracted.textBytes.size ∧
      site.2.2.toNat < 2^31 := by
  cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem reset_branch [Bindings] {v : Variant} {site : Nat × BitVec 4 × BitVec 32}
    (member : site ∈ resetBranchSites v) {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1)
    (outside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Effect.post (fun u => Sha2.Proofs.Reset.Dispatch.branchEffect
        (Extracted.textAddress + BitVec.ofNat 64 site.1) u site.2.2 site.2.1) s t := by
  have valid := resetBranchSites_valid v site member
  have code : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 site.1)
      (Sha2.Proofs.Reset.Dispatch.branchBytes site.2.2 site.2.1)) s := by
    apply programText_slice (programLoaded_codeIn loaded) site.1
    · have bound := valid.1
      change site.1 + 9 < 71757 at bound
      simp only [Sha2.Proofs.Reset.Dispatch.branchBytes, List.length_append,
        encodeTestR64R64, List.length_cons, List.length_nil, immBytes_length]
      omega
    · simpa [Sha2.Proofs.Reset.Dispatch.branchBytes, encodeTestR64R64,
        immBytes_length] using valid.2.1
  have inside : BlockInProgram (Extracted.textAddress + BitVec.ofNat 64 site.1) 9 :=
    blockInProgram_of_textOffset site.1 9 valid.1
  have target : InProgram (Extracted.textAddress + BitVec.ofNat 64 site.1 + 9 +
      site.2.2.signExtend 64) := by
    have finite : ∀ site ∈ resetBranchSites v,
        Extracted.textAddress + BitVec.ofNat 64 site.1 + 9 + site.2.2.signExtend 64 =
        Extracted.textAddress + BitVec.ofNat 64 (site.1 + 9 + site.2.2.toNat) := by
      cases v <;> decide +kernel
    rw [finite site member]
    exact inProgram_of_textOffset _ valid.2.2.1
  obtain ⟨fuel, t, run, readyT, _, post⟩ :=
    Sha2.Proofs.Reset.Dispatch.branch _ boundary outside inside target s ready code rip
  exact ⟨fuel, t, run, readyT, post⟩

def finalizeFirstBranchPC (v : Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 ((ResetLayout.finalizeIntoReset v).textOffset + 0xe0)

set_option maxHeartbeats 1000000 in
theorem finalize_first_branch [Bindings] {v : Variant} {s : RamState}
    {boundary : ReturnBoundary} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = finalizeFirstBranchPC v) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rsi = 0 then finalizeFirstBranchPC v + 5
        else finalizeFirstBranchPC v + 59) ∧ AgreesExcept [.flags, .rip] s t := by
  have code : CodeIn (codeRange (finalizeFirstBranchPC v) [0x48, 0x85, 0xf6, 0x75, 0x36]) s := by
    apply programText_slice (programLoaded_codeIn loaded)
      ((ResetLayout.finalizeIntoReset v).textOffset + 0xe0)
    · cases v <;> decide
    · cases v <;> decide +kernel
  have inside : BlockInProgram (finalizeFirstBranchPC v) 59 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide
  generalize hp : finalizeFirstBranchPC v = p at *
  obtain ⟨u, run, readyU, tested⟩ :=
    (show StepEffect _ _ (testR64R64Effect p 6 6) from
      test_r64_r64_effect_step p 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances ready
      (code.mono (codeRange_mem_of_take (by decide))) rip
      (boundary_ne_program outside (inside 3 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := tested.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) code
  have low : (branchTarget (p + 3) 2 ((54 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := inside 59 (by decide)
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel8_effect_step (p + 3) 5 54 u readyU
    (codeU.mono (codeRange_mem_of_drop 3 (by decide))) ⟨tested.rip, fun _ => low⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi == 0) := by
    have h := tested.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi &&& s.regValue .rsi == 0) at h
    simpa only [BitVec.and_self] using h
  have target : t.RIP = (if s.regValue .rsi = 0 then p + 5 else p + 59) := by
    rw [jumped.rip]
    change (if !(StatusFlags.ofRFLAGS u.RFLAGS).ZF then
      p + 3 + 2 + (54#8).signExtend 64 else p + 3 + 2) = _
    rw [zero]
    by_cases h : s.regValue .rsi = 0 <;> simp [h, BitVec.add_assoc]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (inside 5 (by decide))
    · exact boundary_ne_program outside (inside 59 (by decide))
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])⟩

def traitSecondBranchOffset (v : Variant) : Nat :=
  (ResetLayout.traitFinalizeIntoReset v).textOffset + (ResetLayout.traitFinalizeIntoResetInitializationEnds v)[1]!

def traitSecondBranchDisplacement : Variant → BitVec 32
  | .sha384 => 0x15d
  | .sha512 => 0x15e
  | .sha512_224 => 0x15c
  | .sha512_256 => 0x15b

theorem trait_second_branch [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v))
    (readable : MemReadable s (rspOf s + 8) 8) (outside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Effect.post (fun u => Sha2.Proofs.Reset.TraitFinalizeIntoReset.branchEffect
        (Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v)) u 8
        (traitSecondBranchDisplacement v)) s t := by
  have code : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v))
      (Sha2.Proofs.Reset.TraitFinalizeIntoReset.branchBytes 8 (traitSecondBranchDisplacement v))) s := by
    apply programText_slice (programLoaded_codeIn loaded) (traitSecondBranchOffset v)
    · cases v <;> decide
    · cases v <;> decide +kernel
  have inside : BlockInProgram (Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v)) 12 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide
  have target : InProgram (Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v) +
      (12#64 + (traitSecondBranchDisplacement v).signExtend 64)) := by
    have h := inProgram_of_textOffset ((ResetLayout.traitFinalizeIntoReset v).textOffset +
      ((ResetLayout.traitFinalizeIntoReset v).traversals.map ResetLayout.Traversal.exit)[1]!)
      (by cases v <;> decide)
    cases v <;> exact h
  obtain ⟨fuel, t, run, readyT, _, post⟩ := Sha2.Proofs.Reset.TraitFinalizeIntoReset.branch
    8 (traitSecondBranchDisplacement v) _ boundary outside inside target s ready code ⟨rip, readable⟩
  exact ⟨fuel, t, run, readyT, post⟩

end Sha2.Proofs.Wrapper512.Dispatch
