import P256.Proofs.ReadBe.Memory
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (neg_rsi_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loop_head [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11914e)
    (remaining : 8 ≤ (s.regValue .r13).toNat)
    (writable : MemWritable s (stackPtr s + 16) 8)
    (avoids : ∀ a, Component.Covers (.mem (stackPtr s + 16) 8) a → ¬ InProgram a)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ t.RIP = 0x119110 ∧
      t.regValue .rax = 8 ∧ t.regValue .rsi = -8 ∧
      AgreesExcept [.reg 0, .reg 6, .flags, .rip, .mem (stackPtr s + 16) 8] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, ha1, hr1, he1⟩ :=
    (cmp_r64_imm8_effect_step 0x11914e 0x49 0xfd 8
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice code 0x1914e _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19152 (by decide +kernel)))
  change (cmpR64Imm8Effect 0x11914e 13 8 s).Holds s s1 at he1
  have f1 : AgreesExcept [.flags, .rip] s s1 := he1.agrees
  have ext1 := f1.external (by simp [Component.Covers])
  have cf1 : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = false := by
    have hc := he1.flags.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).CF =
      decide ((s.regValue .r13).toNat < 8) at hc
    exact hc.trans (decide_eq_false (by omega))
  obtain ⟨s2, ha2, hr2, he2⟩ :=
    (mov_r32_imm32_effect_step 0x119152 0xb8 (by decide +kernel) 8).advances hr1
      (programText_slice (code.of_external_eq ext1) 0x19152 _
        (by decide +kernel) (by decide +kernel)) he1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19157 (by decide +kernel)))
  change (movR32Imm32Effect 0x119152 5 0 8 s1).Holds s1 s2 at he2
  have f2 : AgreesExcept [.reg 0, .rip] s1 s2 := he2.agrees
  have ext2 := (f2.external (by simp [Component.Covers])).trans ext1
  have cf2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = false := by
    rw [f2.rflags (by simp) (by simp)]
    exact cf1
  have ax2 : s2.regValue .rax = 8 := he2.writes
  obtain ⟨s3, ha3, hr3, he3⟩ :=
    (cmov_r64_r64_effect_step 0x119157 0x49 0x42 0xc5
      (by simp [RexWPrefix]) (.inl rfl) rfl).advances hr2
      (programText_slice (code.of_external_eq ext2) 0x19157 _
        (by decide +kernel) (by decide +kernel)) he2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1915b (by decide +kernel)))
  change (cmovR64R64Effect 0x119157 2 0 13 s2).Holds s2 s3 at he3
  have f3 : AgreesExcept [.reg 0, .rip] s2 s3 := he3.agrees
  have ext3 := (f3.external (by simp [Component.Covers])).trans ext2
  have ax3 : s3.regValue .rax = 8 := by
    have hw : s3.regValue .rax =
      if (StatusFlags.ofRFLAGS s2.RFLAGS).CF then s2.regValue .r13 else s2.regValue .rax := he3.writes
    simpa only [cf2, Bool.false_eq_true, ↓reduceIte] using hw.trans (by simp [cf2, ax2])
  obtain ⟨s4, ha4, hr4, he4⟩ :=
    (mov_r64_r64_effect_step 0x11915b 0x48 0xc6 (by simp [RexWPrefix]) rfl).advances hr3
      (programText_slice (code.of_external_eq ext3) 0x1915b _
        (by decide +kernel) (by decide +kernel)) he3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1915e (by decide +kernel)))
  change (movR64R64Effect 0x11915b 6 0 s3).Holds s3 s4 at he4
  have f4 : AgreesExcept [.reg 6, .rip] s3 s4 := he4.agrees
  have ext4 := (f4.external (by simp [Component.Covers])).trans ext3
  have si4 : s4.regValue .rsi = 8 := he4.writes.trans ax3
  obtain ⟨s5, ha5, hr5, he5⟩ := (neg_rsi_effect_step 0x11915e).advances hr4
    (programText_slice (code.of_external_eq ext4) 0x1915e _
      (by decide +kernel) (by decide +kernel)) he4.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x19161 (by decide +kernel)))
  have f5 : AgreesExcept [.reg 6, .flags, .rip] s4 s5 := he5.agrees
  have ext5 := (f5.external (by simp [Component.Covers])).trans ext4
  have si5 : s5.regValue .rsi = -8 := by
    have hw : s5.regValue .rsi = -s4.regValue .rsi := he5.writes
    rwa [si4] at hw
  have zf5 : (StatusFlags.ofRFLAGS s5.RFLAGS).ZF = false := by
    have hz := he5.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s5.RFLAGS).ZF = ((0 - s4.regValue .rsi) == 0) at hz
    rw [si4] at hz
    exact hz
  have f05 : AgreesExcept [.reg 0, .reg 6, .flags, .rip] s s5 :=
    ((((f1.trans f2).trans f3).trans f4).trans f5).mono (by simp)
  have rsp5 : stackPtr s5 = stackPtr s := f05.read (n := 64) (r := 4) (by simp)
  have apart : RangeApart (stackPtr s + 16) 8 0x119161 9 := by
    intro i hi j hj he
    apply avoids (stackPtr s + 16 + BitVec.ofNat 64 i) ⟨i, hi, rfl⟩
    rw [he]
    have hp := inProgram_of_textOffset (0x19161+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hp
    exact hp
  obtain ⟨s6, ha6, hr6, he6⟩ :=
    (mov_m64_imm32_effect_step 0x119161 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) rfl rfl 0).advances hr5
      (programText_slice (code.of_external_eq ext5) 0x19161 _
        (by decide +kernel) (by decide +kernel))
      ⟨he5.rip, by
         change MemWritable s5 (stackPtr s5 + 16) 8
         rw [rsp5]
         exact writable.of_external_eq ext5,
       by
         change RangeApart (stackPtr s5 + 16) 8 0x119161 9
         rw [rsp5]
         exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x1916a (by decide +kernel)))
  have f6 : AgreesExcept [.mem (stackPtr s + 16) 8, .rip] s5 s6 := by
    have hf := he6.agrees
    simp only [movM64Imm32Effect_components] at hf
    change AgreesExcept [.mem (stackPtr s5 + 16) 8, .rip] s5 s6 at hf
    rwa [rsp5] at hf
  have loaded6 : ProgramLoaded s6 := by
    intro a b hb
    apply Eq.trans (f6.byte ?_) (by rw [ext5]; exact loaded a b hb)
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact avoids a ha ⟨b, hb⟩
    · exact ha
  have zf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = false := by
    rw [f6.rflags (by simp) (by simp)]
    exact zf5
  have branch : (jccEffect 0x11916a 2 5 ((0xa4 : BitVec 8).signExtend 64) s6).rip =
      0x119110 := by simp [jccEffect, branchEffect, condHolds, zf6, branchTarget]
  obtain ⟨t, ha7, hr7, he7⟩ := (jcc_rel8_effect_step 0x11916a 5 0xa4).advances hr6
    (programText_slice (programLoaded_codeIn loaded6) 0x1916a _
      (by decide +kernel) (by decide +kernel)) ⟨he6.rip, by intro _; decide +kernel⟩
    (by
      rw [branch]
      exact boundary_ne_program outside (inProgram_of_textOffset 0x19110 (by decide +kernel)))
  have f7 : AgreesExcept [.rip] s6 t := he7.agrees
  refine ⟨t, ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans ha7))))),
    hr7, he7.rip.trans branch, ?_, ?_, ((f05.trans f6).trans f7).mono (by simp)⟩
  · exact ((((f4.trans f5).trans f6).trans f7).read (n := 64) (r := 0) (by simp)).trans ax3
  · exact ((f6.trans f7).read (n := 64) (r := 6) (by simp)).trans si5

end P256.Proofs.ReadBe
