import P256.Proofs.HMAC.Pad.Byte

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem advance [Bindings] {loop : Loop} {s : RamState} {boundary : ReturnBoundary}
    {n : Nat} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = loop.address 4)
    (counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + 3)) (hn : n < 16) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if n + 1 < 16 then BitVec.ofNat 64 loop.entry
        else BitVec.ofNat 64 (loop.entry + loop.length)) ∧
      t.regValue .rax = BitVec.ofNat 64 (4 * (n + 1) + 3) ∧
      AgreesExcept [.reg 0, .flags, .rip] s t := by
  have codeAddress (offset : Nat) (bound : offset ≤ 10) :
      InProgram (loop.address 4 + BitVec.ofNat 64 offset) := by
    change InProgram (BitVec.ofNat 64 (loop.entry + loop.position 4) + BitVec.ofNat 64 offset)
    rw [← BitVec.ofNat_add, Nat.add_assoc]
    exact address_inProgram loop _ (by unfold Loop.length; omega)
  obtain ⟨u, run1, readyU, add⟩ :=
    (add_r64_imm8_effect_step (loop.address 4) 0x48 0xc0 4
      (by simp [RexWPrefix]) rfl rfl).advances ready (add_code loaded loop) rip
      (boundary_ne_program outside (codeAddress 4 (by decide)))
  change (addR64Imm8Effect (loop.address 4) 0 4 s).Holds s u at add
  have memU : u.external = s.external := add.agrees.external (by simp [Component.Covers])
  have loadedU : ProgramLoaded u := by intro a b h; rw [memU]; exact loaded a b h
  have counterU : u.regValue .rax = BitVec.ofNat 64 (4 * (n + 1) + 3) := by
    have h : u.regValue .rax = s.regValue .rax + 4 := add.writes
    rw [h, counter]
    change BitVec.ofNat 64 (4 * n + 3) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
  obtain ⟨v, run2, readyV, compare⟩ :=
    (cmp_r64_imm8_effect_step (loop.address 4 + 4) 0x48 0xf8 67
      (by simp [RexWPrefix]) rfl rfl).advances readyU (cmp_code loadedU loop) add.rip
      (by simpa only [cmpR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program outside (codeAddress 8 (by decide)))
  change (cmpR64Imm8Effect (loop.address 4 + 4) 0 67 u).Holds u v at compare
  have memV : v.external = u.external := compare.agrees.external (by simp [Component.Covers])
  have loadedV : ProgramLoaded v := by intro a b h; rw [memV]; exact loadedU a b h
  have flag : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (n + 1 = 16) := by
    have h : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = (u.regValue .rax - 67 == 0) :=
      compare.flags.2.2.2.1
    rw [h, counterU]
    by_cases eq : n + 1 = 16
    · rw [eq]
      decide
    · have ne : BitVec.ofNat 64 (4 * (n + 1) + 3) - 67#64 ≠ 0#64 := by
        intro h
        have he := congrArg (fun x : BitVec 64 => x + 67#64) h
        rw [BitVec.sub_add_cancel, BitVec.zero_add] at he
        have ht := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at ht
        rw [Nat.mod_eq_of_lt (by omega)] at ht
        omega
      simp [ne, eq]
  have target : (jccEffect (loop.address 4 + 8) 2 5 (loop.back.signExtend 64) v).rip =
      (if n + 1 < 16 then BitVec.ofNat 64 loop.entry
        else BitVec.ofNat 64 (loop.entry + loop.length)) := by
    simp only [jccEffect, branchEffect, condHolds, flag]
    by_cases lt : n + 1 < 16
    · have ne : ¬ n + 1 = 16 := by omega
      simp only [ne, decide_false, Bool.not_false, reduceIte, lt, branchTarget]
      exact branch_target loop
    · have eq : n + 1 = 16 := by omega
      simp only [eq, decide_true, Bool.not_true]
      exact branch_end loop
  obtain ⟨t, run3, readyT, branch⟩ :=
    (jcc_rel8_effect_step (loop.address 4 + 8) 5 loop.back).advances readyV
      (by cases loop <;> exact branch_code loadedV _)
      ⟨by change v.RIP = loop.address 4 + 8#64
          simpa only [cmpR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using compare.rip,
        by intro; cases loop <;> decide +kernel⟩
      (by rw [target]; split
          · exact boundary_ne_program outside (by simpa only [Nat.add_zero] using address_inProgram loop 0 (by omega))
          · exact boundary_ne_program outside (address_inProgram loop loop.length (by omega)))
  have frame : AgreesExcept [.reg 0, .flags, .rip] s t :=
    ((add.agrees.trans compare.agrees).trans branch.agrees).mono
      (by simp [jccEffect, branchEffect, Effect.components, addR64Imm8Effect,
        cmpR64Imm8Effect, Write.component, Operand.component])
  refine ⟨t, (run1.trans run2).trans run3, readyT, ?_, branch.rip.trans target, ?_, frame⟩
  · intro a b h
    rw [frame.external (by simp [Component.Covers])]
    exact loaded a b h
  · exact (branch.agrees.read (n := 64) (r := 0) (by simp [jccEffect])).trans
      ((compare.agrees.read (n := 64) (r := 0) (by simp)).trans counterU)

end P256.Proofs.HMAC.Pad
