import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb.Direct (Stage)

theorem select_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .select).length)
    (target : InProgram (p + 33)) :
    AdvanceTriple boundary (Pre p .select) (codeRange p (bytes .select))
      (Effect.post (effect p .select)) := by
  intro s ready loaded pre
  have cmpCode : CodeIn (codeRange p [0x49,0x83,0xfe,0x3f]) s := by
    apply loaded.mono
    x86_sub
  obtain ⟨t, cmpStep, readyT, cmp⟩ := (cmp_r64_imm8_effect_step
    p 0x49 0xfe 63 (by simp [RexWPrefix]) rfl rfl).advances
    (boundary := boundary) ready cmpCode pre.rip
    (boundary_ne_program outside (inside 4 (by decide)))
  have loadedT : CodeIn (codeRange p (bytes .select)) t :=
    cmp.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [cmpR64Imm8Effect, Effect.components, Component.Covers]) loaded
  have branchCode : CodeIn (codeRange (p + 4) [0x77,0x1b]) t := by
    apply loadedT.mono
    x86_sub
  have low : (branchTarget (p + 4) 2 ((27 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  obtain ⟨u, branchStep, readyU, branch⟩ := jcc_rel8_effect_step (p + 4) 7 27
    t readyT branchCode ⟨cmp.rip, fun _ => low⟩
  have cf : (StatusFlags.ofRFLAGS t.RFLAGS).CF = (s.regValue .r14).ult 63 := cmp.flags.1
  have zf : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (s.regValue .r14 - 63 == 0) := cmp.flags.2.2.2.1
  have choose : (!((s.regValue .r14).ult 63 || (s.regValue .r14 - 63 == 0))) =
      decide (¬ (s.regValue .r14).toNat ≤ 63) := by
    have eq : (s.regValue .r14 - 63 == 0) = decide ((s.regValue .r14).toNat = 63) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · exact congrArg BitVec.toNat
      · intro h
        exact BitVec.eq_of_toNat_eq h
    rw [eq]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
      decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
    omega
  have rip : u.RIP = (effect p .select s).rip := by
    rw [branch.rip]
    change (if !((StatusFlags.ofRFLAGS t.RFLAGS).CF || (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      then branchTarget (p + 4) 2 ((27 : BitVec 8).signExtend 64) else (p + 4) + 2) = _
    rw [cf, zf, choose]
    by_cases small : (s.regValue .r14).toNat ≤ 63 <;>
      simp [effect, small, branchTarget, BitVec.add_assoc]
  have run : Advances boundary 1 t u := by
    apply Advances.of_step branchStep
    left
    rw [rip]
    change (if (s.regValue .r14).toNat ≤ 63 then p + 6 else p + 33) ≠ boundary.rip
    split
    · exact boundary_ne_program outside (inside 6 (by decide))
    · exact boundary_ne_program outside target
  refine ⟨2, u, cmpStep.trans run, readyU, ?_, rip, trivial, ?_, ?_⟩
  · exact branch.codeIn (branchEffect_avoids _ _ _ _) loadedT
  · exact ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩
  · apply (cmp.agrees.trans branch.agrees).mono
    simp [cmpR64Imm8Effect, jccEffect, branchEffect, effect, Effect.components]

end Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
