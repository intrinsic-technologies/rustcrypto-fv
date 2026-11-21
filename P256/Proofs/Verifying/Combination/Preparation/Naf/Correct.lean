import P256.Proofs.Verifying.Combination.Preparation.Contract
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct_of_scalar (scalar : Combination.Naf.Serialize.ScalarCorrect) : InlineCorrect := by
  intro bindings s t boundary p q u v pre input tables
  obtain ⟨n1, a, r1, a1⟩ := pack_tables pre tables
  obtain ⟨n2, b, r2, a2⟩ := scalar_copy pre input a1
  obtain ⟨n3, c, r3, a3⟩ := first_recode_input pre a2
  obtain ⟨n4, d, r4, a4⟩ := first_recode scalar pre a3
  obtain ⟨n5, e, r5, a5⟩ := second_scalar_input pre a4
  obtain ⟨n6, f, r6, a6⟩ := second_recode scalar pre a5
  obtain ⟨n7, g, r7, a7⟩ := second_copy_result pre a6
  obtain ⟨n8, h, r8, a8⟩ := third_copy pre a7
  obtain ⟨n9, w, r9, a9⟩ := prepare_metadata pre a8
  exact ⟨n1+n2+n3+n4+n5+n6+n7+n8+n9, w,
    (((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9, a9⟩

theorem correct : InlineCorrect := correct_of_scalar Combination.Naf.Serialize.scalar_correct

end P256.Proofs.Verifying.Combination.Preparation.Naf
