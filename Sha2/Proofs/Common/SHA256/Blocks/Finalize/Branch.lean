import Sha2.Proofs.Common.SHA256.Finalize.Blocks
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

namespace Branch

def comparisonEffect (p : BitVec 64) (v : Variant) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (comparisonBytes v).length
    writes := if v = .reset then [⟨(.reg 3 : Operand 64), rspOf s + 64⟩] else []
    flags := some (.ofStatusFlags (cmpSpec ((.reg v.padReg : Operand 64).read s) 7)) }

attribute [local x86_compose] comparisonBytes comparisonEffect Variant.padReg stackMode

macro "sha256_finalize_comparison " rex:num "," modrm:num "," reset:ident
    "," pc:term "," outside:term "," inside:term : tactic => do
  let begin ← `(tactic| advance_reloc_begin
    (cmp_r64_imm8_effect_step $pc $rex $modrm 7 (by simp [RexWPrefix]) rfl rfl)
    next (boundary_ne_program $outside ($inside 4 (by decide))))
  let mid ← if reset.getId == `yes then `(tactic| advance_reloc_then
    (lea_r64_effect_step ($pc + 4) 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
    next (boundary_ne_program $outside ($inside 9 (by decide)))) else `(tactic| skip)
  `(tactic| ($begin:tactic; $mid:tactic; advance_finish [comparisonEffect]))

theorem comparison_run [Bindings] (p : BitVec 64) (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (comparisonBytes v).length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (comparisonBytes v))
      (Effect.post (comparisonEffect p v)) := by
  cases v with
  | digest => sha256_finalize_comparison 0x49, 0xff, no, p, outside, inside
  | reset => sha256_finalize_comparison 0x48, 0xfb, yes, p, outside, inside
  | finalizeFirst => sha256_finalize_comparison 0x48, 0xfb, no, p, outside, inside
  | finalizeLast => sha256_finalize_comparison 0x49, 0xfe, no, p, outside, inside
  | traitFirst => sha256_finalize_comparison 0x48, 0xfb, no, p, outside, inside
  | traitLast => sha256_finalize_comparison 0x49, 0xfe, no, p, outside, inside

theorem above_seven (value : BitVec 64) :
    (!(value.ult 7 || (value - 7 == 0))) = decide (¬ value.toNat < 8) := by
  have zero : (value - 7 == 0) = decide (value.toNat = 7) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
    constructor
    · intro h
      exact congrArg BitVec.toNat h
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  rw [zero]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
    decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
  omega

theorem bytes_length (v : Variant) (disp : BitVec 32) :
    (bytes v disp).length = (comparisonBytes v).length + 6 := by
  simp [bytes]

theorem run [Bindings] (p : BitVec 64) (v : Variant) (disp : BitVec 32)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (bytes v disp).length)
    (target : InProgram
      (branchTarget (p + BitVec.ofNat 64 (comparisonBytes v).length) 6 (disp.signExtend 64))) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (bytes v disp))
      (Effect.post (effect p v disp)) := by
  intro s ready loaded rip
  have before : CodeIn (codeRange p (comparisonBytes v)) s := by
    apply loaded.mono
    intro x hx
    rw [bytes, List.append_assoc, codeRange_append]
    exact List.mem_append_left _ hx
  obtain ⟨fuel, t, run, readyT, _, compare⟩ := comparison_run p v boundary outside
    (fun i hi => inside i (by rw [bytes_length]; omega)) s ready before rip
  have loadedT : CodeIn (codeRange p (bytes v disp)) t := by
    apply compare.codeIn _ loaded
    apply Effect.Avoids.of_noMem
    cases v <;> simp [comparisonEffect, Effect.components, Component.Covers]
  have branchCode : CodeIn
      (codeRange (p + BitVec.ofNat 64 (comparisonBytes v).length)
        ([0x0f,0x87] ++ immBytes 32 disp)) t := by
    apply loadedT.mono
    intro x hx
    rw [bytes, List.append_assoc, codeRange_append]
    exact List.mem_append_right _ hx
  have targetLow : (branchTarget (p + BitVec.ofNat 64 (comparisonBytes v).length)
      6 (disp.signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    exact programSections_low.codeLow (_, byte) mem
  obtain ⟨u, step, readyU, result⟩ := jcc_rel32_effect_step
    (p + BitVec.ofNat 64 (comparisonBytes v).length) 7 disp t readyT branchCode
      ⟨compare.rip, fun _ => targetLow⟩
  have carry : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
      ((.reg v.padReg : Operand 64).read s).ult 7 := compare.flags.1
  have zero : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      ((.reg v.padReg : Operand 64).read s - 7 == 0) := compare.flags.2.2.2.1
  have nextRip : u.RIP = (effect p v disp s).rip := by
    rw [result.rip]
    change (if !((StatusFlags.ofRFLAGS t.RFLAGS).CF || (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      then branchTarget (p + BitVec.ofNat 64 (comparisonBytes v).length) 6 (disp.signExtend 64)
      else (p + BitVec.ofNat 64 (comparisonBytes v).length) + 6) = _
    rw [carry, zero, above_seven]
    rw [effect, bytes_length, BitVec.ofNat_add, BitVec.add_assoc]
    by_cases small : ((.reg v.padReg : Operand 64).read s).toNat < 8 <;>
      simp only [small, decide_true, decide_false, Bool.false_eq_true,
        not_true_eq_false, not_false_eq_true, ↓reduceIte] <;> rfl
  have advances : Advances boundary 1 t u := by
    apply Advances.of_step step
    left
    rw [nextRip]
    change (if ((.reg v.padReg : Operand 64).read s).toNat < 8 then _ else _) ≠ _
    split
    · exact boundary_ne_program outside (inside _ (Nat.le_refl _))
    · exact boundary_ne_program outside target
  refine ⟨fuel + 1, u, run.trans advances, readyU, ?_, nextRip, ?_, ?_, ?_⟩
  · apply result.codeIn _ loadedT
    exact branchEffect_avoids _ _ _ _
  · by_cases reset : v = .reset
    · subst v
      change (.reg 3 : Operand 64).read u = rspOf s + 64
      rw [result.agrees.read (by simp [jccEffect, branchEffect, Effect.components])]
      exact compare.writes
    · simp only [effect, reset, ↓reduceIte, Write.AllHold]
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (compare.agrees.trans result.agrees).mono
    cases v <;> simp [comparisonEffect, effect, jccEffect, branchEffect, Effect.components]

end Branch
end Sha2.Proofs.Common.SHA256.Finalize
