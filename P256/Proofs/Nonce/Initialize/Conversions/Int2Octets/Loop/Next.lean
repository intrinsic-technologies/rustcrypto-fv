import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

theorem next [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (index : s.regValue .rbp = BitVec.ofNat 64 i) (count : s.regValue .r15 = 4)
    (hi : i ≤ 4) (rip : s.RIP = 0x10708b) :
    ∃ t, Stage initial t boundary ∧
      t.RIP = (if i < 4 then 0x107050 else 0x107093) ∧
      t.regValue .rdx = s.regValue .rbx ∧
      AgreesExcept [.reg 2, .flags, .rip] s t := by
  obtain ⟨u, run1, ready1, effect1⟩ :=
    (mov_r64_r64_effect_step 0x10708b 0x48 0xda (by simp [RexWPrefix]) rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x708b _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x708e (by decide)))
  have loaded1 := effect1.agrees.codeIn
    (by simp [Component.Covers]) (programLoaded_codeIn stage.loaded)
  obtain ⟨v, run2, ready2, effect2⟩ :=
    (cmp_r64_r64_effect_step 0x10708e 0x49 0xef (by simp [RexWPrefix]) rfl).advances
      ready1 (programText_slice loaded1 0x708e _ (by decide) (by decide +kernel)) effect1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7091 (by decide)))
  have index1 : u.regValue .rbp = BitVec.ofNat 64 i :=
    (effect1.agrees.read (n := 64) (r := 5) (by simp [gprNumber, rexB, modrmRm])).trans index
  have count1 : u.regValue .r15 = 4 :=
    (effect1.agrees.read (n := 64) (r := 15) (by simp [gprNumber, rexB, modrmRm])).trans count
  have zero : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (i = 4) := by
    have hz : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
        (u.regValue .r15 - u.regValue .rbp == 0) := effect2.flags.2.2.2.1
    rw [hz, index1, count1]
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide
  have loaded2 := effect2.agrees.codeIn
    (by simp [Component.Covers]) loaded1
  obtain ⟨t, step3, ready3, effect3⟩ :=
    jcc_rel8_effect_step 0x107091 5 0xbd v ready2
      (programText_slice loaded2 0x7091 _ (by decide) (by decide +kernel))
      ⟨effect2.rip, by intro; decide⟩
  have target : (jccEffect 0x107091 2 5 ((0xbd : BitVec 8).signExtend 64) v).rip =
      if i < 4 then 0x107050 else 0x107093 := by
    simp only [jccEffect, branchEffect, condHolds, zero]
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp [branchTarget]
  have run3 : Advances boundary 1 v t := Advances.of_step step3 (.inl (by
    rw [effect3.rip, target]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7050 (by decide))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7093 (by decide))))
  have agrees : AgreesExcept [.reg 2, .flags, .rip] s t :=
    ((effect1.agrees.trans effect2.agrees).trans effect3.agrees).mono
      (by simp [movR64R64Effect, cmpR64R64Effect, jccEffect, branchEffect,
        Effect.components, Write.component, Operand.component, gprNumber, rexB, rexR,
        modrmRm, modrmReg])
  refine ⟨t, stage.of_agrees pre (run1.trans (run2.trans run3)) ready3 agrees ?_ ?_ (by simp),
    effect3.rip.trans target, ?_, agrees⟩
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact False.elim ha
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact fun h => h
  · exact (effect3.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans
      ((effect2.agrees.read (n := 64) (r := 2) (by simp)).trans effect1.writes)

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
