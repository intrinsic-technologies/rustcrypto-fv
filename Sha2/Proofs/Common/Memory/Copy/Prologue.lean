import Sha2.Proofs.Common.Memory.Copy.RegisterOps
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple

set_option autoImplicit false

open Sha2.Proofs.Program

open Sha2.Proofs.Common.Instructions (cmovbR8RdxEffect cmovb_r8_rdx_effect_step negR8dEffect neg_r8d_effect_step)
open Sha2.Proofs.Common.Machine (boundary_ne_program inProgram_of_textOffset programText_slice)

namespace Sha2.Proofs.Common.Memory

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memcpy_alignment_count (x : BitVec 64) :
    ((-x.setWidth 32) &&& (7 : BitVec 32)).setWidth 64 =
      BitVec.ofNat 64 ((8 - x.toNat % 8) % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (-x.setWidth 32).toNat &&& (2^3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_neg, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  have h32 := Nat.mod_lt x.toNat (show 0 < 4294967296 by decide)
  have h8 := Nat.mod_lt x.toNat (show 0 < 8 by decide)
  have hm := Nat.mod_mod_of_dvd x.toNat (show 8 ∣ 4294967296 by decide)
  have hn := Nat.mod_mod_of_dvd (4294967296 - x.toNat % 4294967296)
    (show 8 ∣ 4294967296 by decide)
  omega

end Sha2.Proofs.Common.Memory

namespace Sha2.Proofs.Common.Memory
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memcpy_prologue [Bindings]
    {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10dd60)
    (hn : s.regValue .rdx = BitVec.ofNat 64 n) (hbound : n < 2^64) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x10dd77 ∧
      t.regValue .r8 = BitVec.ofNat 64 (min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) ∧
      t.regValue .rcx = BitVec.ofNat 64 (min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) ∧
      AgreesExcept [.reg 0, .reg 1, .reg 8, .flags, .rip] s t := by
  have step1 : StepEffect (fun s => s.RIP = 0x10dd60)
      (codeRange 0x10dd60 [0x48, 0x89, 0xf8]) (movR64R64Effect 0x10dd60 0 7) :=
    mov_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide +kernel)
  obtain ⟨s1, ha1, hr1, he1⟩ := step1.advances hready
    (programText_slice hcode 0xdd60 _ (by decide) (by decide +kernel)) hip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd63 (by decide)))
  have hc1 := he1.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hcode
  have step2 : StepEffect (fun s => s.RIP = 0x10dd63)
      (codeRange 0x10dd63 [0x41, 0x89, 0xc0]) (movR32R32Effect 0x10dd63 3 8 0) :=
    mov_r32_r32_rex_effect_step _ _ _ (by simp [RexNoWPrefix]) (by decide +kernel)
  obtain ⟨s2, ha2, hr2, he2⟩ := step2.advances hr1
    (programText_slice hc1 0xdd63 _ (by decide) (by decide +kernel)) he1.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd66 (by decide)))
  have hc2 := he2.codeIn
    (Effect.Avoids.of_noMem (by simp [movR32R32Effect, Effect.components, Component.Covers]) _) hc1
  obtain ⟨s3, ha3, hr3, he3⟩ := (neg_r8d_effect_step 0x10dd66).advances hr2
    (programText_slice hc2 0xdd66 _ (by decide) (by decide +kernel)) he2.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd69 (by decide)))
  have hc3 := he3.codeIn
    (Effect.Avoids.of_noMem (by simp [negR8dEffect, Effect.components, Component.Covers]) _) hc2
  have step4 : StepEffect (fun s => s.RIP = 0x10dd69)
      (codeRange 0x10dd69 [0x41, 0x83, 0xe0, 0x07]) (andR32Imm8Effect 0x10dd69 4 8 7) :=
    and_r32_imm8_rex_effect_step 0x10dd69 0x41 0xe0 7 (by simp [RexNoWPrefix]) (by decide +kernel) (by decide +kernel)
  obtain ⟨s4, ha4, hr4, he4⟩ := step4.advances hr3
    (programText_slice hc3 0xdd69 _ (by decide) (by decide +kernel)) he3.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd6d (by decide)))
  have hc4 := he4.codeIn
    (Effect.Avoids.of_noMem (by simp [andR32Imm8Effect, Effect.components, Component.Covers]) _) hc3
  have step5 : StepEffect (fun s => s.RIP = 0x10dd6d)
      (codeRange 0x10dd6d [0x4c, 0x39, 0xc2]) (cmpR64R64Effect 0x10dd6d 2 8) :=
    cmp_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide +kernel)
  obtain ⟨s5, ha5, hr5, he5⟩ := step5.advances hr4
    (programText_slice hc4 0xdd6d _ (by decide) (by decide +kernel)) he4.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd70 (by decide)))
  have hc5 := he5.codeIn
    (Effect.Avoids.of_noMem (by simp [cmpR64R64Effect, Effect.components, Component.Covers]) _) hc4
  obtain ⟨s6, ha6, hr6, he6⟩ := (cmovb_r8_rdx_effect_step 0x10dd70).advances hr5
    (programText_slice hc5 0xdd70 _ (by decide) (by decide +kernel)) he5.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd74 (by decide)))
  have hc6 := he6.codeIn
    (Effect.Avoids.of_noMem (by simp [cmovbR8RdxEffect, Effect.components, Component.Covers]) _) hc5
  have step7 : StepEffect (fun s => s.RIP = 0x10dd74)
      (codeRange 0x10dd74 [0x4c, 0x89, 0xc1]) (movR64R64Effect 0x10dd74 1 8) :=
    mov_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide +kernel)
  obtain ⟨s7, ha7, hr7, he7⟩ := step7.advances hr6
    (programText_slice hc6 0xdd74 _ (by decide) (by decide +kernel)) he6.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd77 (by decide)))
  have hc7 := he7.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hc6
  have hf := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
    (he4.agrees.trans (he5.agrees.trans (he6.agrees.trans he7.agrees)))))
  have hframe : AgreesExcept [.reg 0, .reg 1, .reg 8, .flags, .rip] s s7 :=
    hf.mono (by simp [movR64R64Effect, movR32R32Effect, negR8dEffect, andR32Imm8Effect,
      cmpR64R64Effect, cmovbR8RdxEffect, Effect.components])
  have hx1 : s1.regValue .rax = s.regValue .rdi := he1.writes
  have hx2 : s2.regValue .r8 = ((s1.regValue .rax).setWidth 32).setWidth 64 := he2.writes
  have hx3 : s3.regValue .r8 = (-((s2.regValue .r8).setWidth 32)).setWidth 64 := he3.writes
  have hx4 : s4.regValue .r8 = (((s3.regValue .r8).setWidth 32) &&& (7 : BitVec 32)).setWidth 64 := he4.writes
  have hx4' : s4.regValue .r8 = BitVec.ofNat 64 ((8 - (s.regValue .rdi).toNat % 8) % 8) := by
    rw [hx4, hx3, hx2, hx1]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
    exact memcpy_alignment_count _
  have hn4 : s4.regValue .rdx = BitVec.ofNat 64 n := by
    have h := (he1.agrees.trans (he2.agrees.trans (he3.agrees.trans he4.agrees))).read
      (r := 2) (n := 64) (by simp [movR64R64Effect, movR32R32Effect, negR8dEffect, andR32Imm8Effect, Effect.components])
    exact h.trans hn
  have hx5 : s5.regValue .r8 = s4.regValue .r8 := he5.agrees.read (n := 64) (r := 8) (by simp)
  have hn5 : s5.regValue .rdx = s4.regValue .rdx := he5.agrees.read (n := 64) (r := 2) (by simp)
  have hcf : (StatusFlags.ofRFLAGS s5.RFLAGS).CF =
      decide ((s4.regValue .rdx).toNat < (s4.regValue .r8).toNat) := he5.flags.1
  have hx6 : s6.regValue .r8 =
      (if (StatusFlags.ofRFLAGS s5.RFLAGS).CF then s5.regValue .rdx else s5.regValue .r8) := he6.writes
  have hx6' : s6.regValue .r8 =
      BitVec.ofNat 64 (min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) := by
    rw [hx6, hcf, hx5, hn5, hx4', hn4]
    have h8 : (8 - (s.regValue .rdi).toNat % 8) % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases hlt : n < (8 - (s.regValue .rdi).toNat % 8) % 8
    · simp [hlt, Nat.min_eq_left (Nat.le_of_lt hlt)]
    · simp [hlt, Nat.min_eq_right (Nat.le_of_not_gt hlt)]
  have hx7 : s7.regValue .r8 = s6.regValue .r8 := he7.agrees.read (n := 64) (r := 8) (by simp)
  have hc7' : s7.regValue .rcx = s6.regValue .r8 := he7.writes
  exact ⟨s7, ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans ha7))))),
    hr7, hc7, he7.rip, hx7.trans hx6', hc7'.trans hx6', hframe⟩

end Sha2.Proofs.Common.Memory
