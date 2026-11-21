import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory
import P256.Proofs.Common.Instructions.CmovAboveEqual
import P256.Proofs.Verifying.Combination.Naf.Machine.RecodeBranchArithmetic
import P256.Proofs.Common.Encoding.Serialize.Convert.AddLoad
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Common.Instructions

set_option maxHeartbeats 600000 in
theorem odd_skip [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i w : Nat}
    (pre : Pre s boundary) (frame : FrameState s t) (index : i < 256)
    (rip : t.RIP = 0x10f499) (r12 : t.regValue .r12 = 5)
    (r13 : t.regValue .r13 = BitVec.ofNat 64 (carry w))
    (rbp : t.regValue .rbp = -BitVec.ofNat 64 i)
    (bits : memLoad t.external (stackPtr t+24) 64 = 256) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10f4ac ∧
      u.regValue .rbp = BitVec.ofNat 64 (skip (256-i) w) ∧
      (StatusFlags.ofRFLAGS u.RFLAGS).CF = decide (skip (256-i) w < 2) ∧
      AgreesExcept [.reg 5, .flags, .rip] t u := by
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a, ra, readyA, ea⟩ :=
    (add_r64_m64_effect_step 0x10f499 0x48 (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xf499 _ (by decide) (by decide +kernel))
      ⟨rip, stack_readable pre.toCalleePre frame (by decide : 24+8 ≤ 136)⟩
      (next 0xf49e (by decide))
  have ga : AgreesExcept [.reg 5, .flags, .rip] t a := ea.agrees
  have fa := frame.after_registers readyA ga (by simp [Component.Covers]) (by simp)
  have bpA : a.regValue .rbp = -BitVec.ofNat 64 i+256 := by
    have h : a.regValue .rbp = t.regValue .rbp+memLoad t.external (stackPtr t+24) 64 := ea.writes
    rw [rbp, bits] at h
    exact h
  have r13A : a.regValue .r13 = BitVec.ofNat 64 (carry w) :=
    (ga.read (n := 64) (r := 13) (by simp)).trans r13
  obtain ⟨b, rb, readyB, eb⟩ :=
    (sub_r64_r64_effect_step 0x10f49e 0x4c 0xed (by simp [RexWPrefix]) rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0xf49e _ (by decide) (by decide +kernel))
      ea.rip (next 0xf4a1 (by decide))
  have gb : AgreesExcept [.reg 5, .flags, .rip] a b := eb.agrees
  have fb := fa.after_registers readyB gb (by simp [Component.Covers]) (by simp)
  have bpB : b.regValue .rbp = -BitVec.ofNat 64 i+256-BitVec.ofNat 64 (carry w) := by
    have h : b.regValue .rbp = a.regValue .rbp-a.regValue .r13 := eb.writes
    rw [bpA, r13A] at h
    exact h
  have r12B : b.regValue .r12 = 5 :=
    ((ga.trans gb).read (n := 64) (r := 12) (by simp)).trans r12
  obtain ⟨d, rd, readyD, ed⟩ :=
    (cmp_r64_r64_effect_step 0x10f4a1 0x4c 0xe5 (by simp [RexWPrefix]) rfl).advances readyB
      (programText_slice (programLoaded_codeIn fb.loaded) 0xf4a1 _ (by decide) (by decide +kernel))
      eb.rip (next 0xf4a4 (by decide))
  have gd : AgreesExcept [.flags, .rip] b d := ed.agrees
  have fd := fb.after_registers readyD gd (by simp [Component.Covers]) (by simp)
  have cfD : (StatusFlags.ofRFLAGS d.RFLAGS).CF = (b.regValue .rbp).ult 5#64 := by
    have h : _ = decide ((b.regValue .rbp).toNat < (b.regValue .r12).toNat) := ed.flags.1
    rw [r12B] at h
    exact h
  obtain ⟨e, re, readyE, ee⟩ :=
    (cmovae_r64_r64_effect_step 0x10f4a4 0x49 0x43 0xec (by simp [RexWPrefix]) rfl rfl).advances readyD
      (programText_slice (programLoaded_codeIn fd.loaded) 0xf4a4 _ (by decide) (by decide +kernel))
      ed.rip (next 0xf4a8 (by decide))
  have ge : AgreesExcept [.reg 5, .rip] d e := ee.agrees
  have fe := fd.after_registers readyE ge (by simp [Component.Covers]) (by simp)
  have bpE : e.regValue .rbp = BitVec.ofNat 64 (skip (256-i) w) := by
    have bpD : d.regValue .rbp = b.regValue .rbp := gd.read (n := 64) (r := 5) (by simp)
    have r12D : d.regValue .r12 = 5 := (gd.read (n := 64) (r := 12) (by simp)).trans r12B
    have h : e.regValue .rbp = cmovR64R64Value 3 5 12 d := ee.writes
    change e.regValue .rbp = (if !(StatusFlags.ofRFLAGS d.RFLAGS).CF then d.regValue .r12 else d.regValue .rbp) at h
    rw [cfD, bpD, r12D, bpB] at h
    apply h.trans
    cases small : (-BitVec.ofNat 64 i+256-BitVec.ofNat 64 (carry w)).ult 5#64 <;>
      simpa only [small, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
        using remaining_skip (w := w) index
  obtain ⟨u, ru, readyU, eu⟩ :=
    (cmp_r64_imm8_effect_step 0x10f4a8 0x48 0xfd 2 (by simp [RexWPrefix]) rfl rfl).advances readyE
      (programText_slice (programLoaded_codeIn fe.loaded) 0xf4a8 _ (by decide) (by decide +kernel))
      ee.rip (next 0xf4ac (by decide))
  have gu : AgreesExcept [.flags, .rip] e u := eu.agrees
  have fu := fe.after_registers readyU gu (by simp [Component.Covers]) (by simp)
  refine ⟨_, u, ((((ra.trans rb).trans rd).trans re).trans ru), fu, eu.rip,
    (gu.read (n := 64) (r := 5) (by simp)).trans bpE, ?_,
    ((((ga.trans gb).trans gd).trans ge).trans gu).mono (by simp)⟩
  have h : (StatusFlags.ofRFLAGS u.RFLAGS).CF = decide ((e.regValue .rbp).toNat < 2) := eu.flags.1
  rw [bpE] at h
  have bound : skip (256-i) w ≤ 5 := Nat.min_le_left _ _
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : skip (256-i) w < 2^64)] using h

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
