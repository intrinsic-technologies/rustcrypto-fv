import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Tail

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_copy [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x106e5d)
    (length : s.regValue .r15 = 65) (capacity : 105 ≤ (s.regValue .rbx).toNat) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ t.RIP = 0x106e76 ∧
      t.regValue .rdi = s.regValue .r14+40 ∧ t.regValue .rsi = stackPtr s+8 ∧
      t.regValue .rdx = 65 ∧ AgreesExcept [.reg 6,.reg 7,.reg 2,.flags,.rip] s t := by
  obtain ⟨s2,a2,r2,e2⟩ := (lea_r64_effect_step 0x106e5d 0x49
    (by simp [RexWPrefix]) 6 (.base 15 (.d8 40)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6e5d _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e61 (by decide)))
  have g2 : AgreesExcept [.reg 6,.rip] s s2 := e2.agrees
  have m2 := g2.external (by simp [Component.Covers])
  have si2 : s2.regValue .rsi = 105 := by
    have h : s2.regValue .rsi = s.regValue .r15+40 := e2.writes
    rw [h,length]
    rfl
  have bx2 : s2.regValue .rbx = s.regValue .rbx := g2.read (n := 64) (r := 3) (by simp)
  obtain ⟨s3,a3,r3,e3⟩ := (cmp_r64_r64_effect_step 0x106e61 0x48 0xde
    (by simp [RexWPrefix]) (by decide)).advances r2
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m2)
      0x6e61 _ (by decide) (by decide +kernel)) e2.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e64 (by decide)))
  have g3 : AgreesExcept [.flags,.rip] s2 s3 := e3.agrees
  have m3 := (g2.trans g3).external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = decide (105 < (s.regValue .rbx).toNat) := by
    have h := e3.flags.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).CF = decide ((s2.regValue .rsi).toNat < (s2.regValue .rbx).toNat) at h
    rw [h,si2,bx2]
    rfl
  have zf : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = decide ((105 : BitVec 64)-s.regValue .rbx = 0) := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = decide (s2.regValue .rsi-s2.regValue .rbx = 0) at h
    rw [h,si2,bx2]
  have cond : condHolds 7 (StatusFlags.ofRFLAGS s3.RFLAGS) = false := by
    change (!((StatusFlags.ofRFLAGS s3.RFLAGS).CF || (StatusFlags.ofRFLAGS s3.RFLAGS).ZF)) = false
    rw [cf,zf]
    by_cases h : 105 < (s.regValue .rbx).toNat
    · simp only [h,decide_true,Bool.true_or,Bool.not_true]
    · have eq : s.regValue .rbx = 105 := BitVec.eq_of_toNat_eq (by change _ = 105; omega)
      rw [eq]
      decide
  obtain ⟨s4,step,r4,raw⟩ := jcc_rel32_effect_step 0x106e64 7 0x9f s3 r3
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m3)
      0x6e64 _ (by decide) (by decide +kernel)) ⟨e3.rip,by intro; decide⟩
  have e4 := jccEffect_not_taken cond raw
  have a4 : Advances boundary 1 s3 s4 := Advances.of_step step (.inl (by
    rw [e4.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6e6a (by decide))))
  have g4 : AgreesExcept [.rip] s3 s4 := e4.agrees
  have m4 := ((g2.trans g3).trans g4).external (by simp [Component.Covers])
  obtain ⟨s5,a5,r5,e5⟩ := (lea_r64_effect_step 0x106e6a 0x49 (by simp [RexWPrefix]) 7
    (.base 14 (.d8 40)) (by decide) rfl rfl).advances r4
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m4)
      0x6e6a _ (by decide) (by decide +kernel)) e4.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e6e (by decide)))
  have g5 : AgreesExcept [.reg 7,.rip] s4 s5 := e5.agrees
  have m5 := (((g2.trans g3).trans g4).trans g5).external (by simp [Component.Covers])
  have di5 : s5.regValue .rdi = s.regValue .r14+40 := by
    have h : s5.regValue .rdi = s4.regValue .r14+40 := e5.writes
    rw [h]
    congr 1
    exact ((g2.trans g3).trans g4).read (n := 64) (r := 14) (by simp)
  obtain ⟨s6,a6,r6,e6⟩ := (lea_r64_effect_step 0x106e6e 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances r5
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m5)
      0x6e6e _ (by decide) (by decide +kernel)) e5.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e73 (by decide)))
  have g6 : AgreesExcept [.reg 6,.rip] s5 s6 := e6.agrees
  have m6 := ((((g2.trans g3).trans g4).trans g5).trans g6).external (by simp [Component.Covers])
  have si6 : s6.regValue .rsi = stackPtr s+8 := by
    have h : s6.regValue .rsi = stackPtr s5+8 := e6.writes
    rw [h]
    congr 1
    exact (((g2.trans g3).trans g4).trans g5).read (n := 64) (r := 4) (by simp)
  obtain ⟨t,a7,rt,e7⟩ := (mov_r64_r64_effect_step 0x106e73 0x4c 0xfa
    (by simp [RexWPrefix]) (by decide)).advances r6
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m6)
      0x6e73 _ (by decide) (by decide +kernel)) e6.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e76 (by decide)))
  have g7 : AgreesExcept [.reg 2,.rip] s6 t := e7.agrees
  refine ⟨t,((((a2.trans a3).trans a4).trans a5).trans a6).trans a7,
    rt,e7.rip,(g6.trans g7).read (n := 64) (r := 7) (by simp) |>.trans di5,
    (g7.read (n := 64) (r := 6) (by simp)).trans si6,?_,
    (((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).mono (by simp)⟩
  exact e7.writes.trans (((((g2.trans g3).trans g4).trans g5).trans g6).read
    (n := 64) (r := 15) (by simp) |>.trans length)

end P256.Proofs.Generate.Wrapper.Tail
