import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1018b7)
    (capacity : (s.regValue .r15 ||| 8).toNat ≤ (s.regValue .r14).toNat) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x1018c3 ∧
      AgreesExcept [.reg 6, .flags, .rip] s t := by
  obtain ⟨a, runA, readyA, effectA⟩ := (mov_r64_r64_effect_step 0x1018b7 0x4c 0xfe
    (by simp [RexWPrefix]) rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x18b7 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x18ba (by decide)))
  have agreesA : AgreesExcept [.reg 6, .rip] s a := effectA.agrees
  have memoryA := agreesA.external (by simp [Component.Covers])
  have siA : a.regValue .rsi = s.regValue .r15 := effectA.writes
  obtain ⟨b, runB, readyB, effectB⟩ := (or_r64_imm8_effect_step 0x1018ba 0x48 0xce 8
    (by simp [RexWPrefix]) rfl rfl).advances readyA
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memoryA)
      0x18ba _ (by decide) (by decide +kernel)) effectA.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x18be (by decide)))
  have agreesB : AgreesExcept [.reg 6, .flags, .rip] a b := effectB.agrees
  have memoryB := (agreesA.trans agreesB).external (by simp [Component.Covers])
  have siB : b.regValue .rsi = s.regValue .r15 ||| 8 := by
    have value : b.regValue .rsi = a.regValue .rsi ||| 8 := effectB.writes
    rwa [siA] at value
  have bpB : b.regValue .r14 = s.regValue .r14 :=
    (agreesA.trans agreesB).read (n := 64) (r := 14) (by simp)
  obtain ⟨c, runC, readyC, effectC⟩ := (cmp_r64_r64_effect_step 0x1018be 0x4c 0xf6
    (by simp [RexWPrefix]) rfl).advances readyB
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memoryB)
      0x18be _ (by decide) (by decide +kernel)) effectB.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x18c1 (by decide)))
  have agreesC : AgreesExcept [.flags, .rip] b c := effectC.agrees
  have memoryC := ((agreesA.trans agreesB).trans agreesC).external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS c.RFLAGS).CF =
      decide ((s.regValue .r15 ||| 8).toNat < (s.regValue .r14).toNat) := by
    have h := effectC.flags.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).CF = decide ((b.regValue .rsi).toNat < (b.regValue .r14).toNat) at h
    rwa [siB, bpB] at h
  have zf : (StatusFlags.ofRFLAGS c.RFLAGS).ZF =
      decide ((s.regValue .r15 ||| 8) - s.regValue .r14 = 0) := by
    have h := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = decide (b.regValue .rsi - b.regValue .r14 = 0) at h
    rwa [siB, bpB] at h
  have condition : condHolds 7 (StatusFlags.ofRFLAGS c.RFLAGS) = false := by
    change (!((StatusFlags.ofRFLAGS c.RFLAGS).CF || (StatusFlags.ofRFLAGS c.RFLAGS).ZF)) = false
    rw [cf, zf]
    by_cases less : (s.regValue .r15 ||| 8).toNat < (s.regValue .r14).toNat
    · simp only [less, decide_true, Bool.true_or, Bool.not_true]
    · have equal : s.regValue .r15 ||| 8 = s.regValue .r14 := BitVec.eq_of_toNat_eq (by omega)
      have zero : (s.regValue .r15 ||| 8) - s.regValue .r14 = 0 :=
        (congrArg (fun x : BitVec 64 => x - s.regValue .r14) equal).trans (BitVec.sub_self _)
      have truth : decide ((s.regValue .r15 ||| 8) - s.regValue .r14 = 0) = true :=
        decide_eq_true zero
      simp only [truth, Bool.or_true, Bool.not_true]
  obtain ⟨t, step, final, raw⟩ := jcc_rel8_effect_step 0x1018c1 7 0x27 c readyC
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memoryC)
      0x18c1 _ (by decide) (by decide +kernel)) ⟨effectC.rip, by intro; decide⟩
  have effect := jccEffect_not_taken condition raw
  have run : Advances boundary 1 c t := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x18c3 (by decide))))
  exact ⟨t, ((runA.trans runB).trans runC).trans run, final, effect.rip,
    (((agreesA.trans agreesB).trans agreesC).trans effect.agrees).mono (by simp)⟩

end P256.Proofs.Sec1.Wrapper.Success.Tail
