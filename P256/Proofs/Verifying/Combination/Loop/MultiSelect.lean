import P256.Proofs.Verifying.Combination.Loop.MultiLength
import P256.Proofs.Common.Curve.LinearCombination.Loop.Cmova
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem select_length [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {u v : Nat} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f100)
    (ptr : t.regValue .rsi = digits + 272) (offset : t.regValue .rdi = 0)
    (left : t.regValue .rbx = BitVec.ofNat 64 (Naf.digits u).length)
    (right : memLoad t.external (digits + 272) 64 = BitVec.ofNat 64 (Naf.digits v).length)
    (hu : u < 2^256) (hv : v < 2^256) :
    ∃ w, Advances boundary 4 t w ∧ State s w ∧ w.RIP = 0x10f10e ∧
      w.regValue .rbx = BitVec.ofNat 64 (max (Naf.digits u).length (Naf.digits v).length) ∧
      AgreesExcept [.reg 10, .reg 3, .flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_r64_effect_step 0x10f100 0x49 0xda (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf100 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf103 (by decide)))
  have frameA : AgreesExcept [.reg 10, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have ptrA : a.regValue .rsi = digits + 272 :=
    (frameA.read (n := 64) (r := 6) (by simp)).trans ptr
  have offsetA : a.regValue .rdi = 0 := (frameA.read (n := 64) (r := 7) (by simp)).trans offset
  have addrA : a.regValue .rsi + (a.regValue .rdi <<< 0) + 0 = digits + 272 := by
    rw [ptrA, offsetA, BitVec.shiftLeft_zero]
    change (digits + 272) + 0#64 + 0#64 = digits + 272
    rw [BitVec.add_zero, BitVec.add_zero]
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_r64_m64_effect_step 0x10f103 0x48 (by simp [RexWPrefix]) 3
      (.sib 6 (some 7) 0 .none) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf103 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemReadable a (a.regValue .rsi + (a.regValue .rdi <<< 0) + 0) 8
        rw [addrA]
        apply readable_of_grow (s := s) _ stateA.allocated
        have bound : digits.toNat + 544 < 2^32 := pre.digitsBounded
        have addr : (digits + 272).toNat = digits.toNat + 272 := by
          change (digits + 272#64).toNat = digits.toNat + 272
          rw [BitVec.toNat_add]
          change (digits.toNat + 272) % 2^64 = digits.toNat + 272
          omega
        apply memoryRegion_memReadable pre.digitsBounded pre.digitsAllocated
        · change digits.toNat ≤ _
          rw [addr]; omega
        · change _ + 8 ≤ digits.toNat + 544
          rw [addr]; omega⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf107 (by decide)))
  have frameB : AgreesExcept [.reg 3, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB frameB (by simp [Component.Covers]) (by simp)
  have bxB : b.regValue .rbx = BitVec.ofNat 64 (Naf.digits v).length := by
    have h := effectB.writes
    change b.regValue .rbx = memLoad a.external (a.regValue .rsi + (a.regValue .rdi <<< 0) + 0) 64 at h
    rw [addrA, frameA.external (by simp [Component.Covers])] at h
    exact h.trans right
  have r10B : b.regValue .r10 = BitVec.ofNat 64 (Naf.digits u).length :=
    (frameB.read (n := 64) (r := 10) (by simp)).trans (effectA.writes.trans left)
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (cmp_r64_r64_effect_step 0x10f107 0x49 0xda (by simp [RexWPrefix]) rfl).advances readyB
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf107 _
        (by decide) (by decide +kernel)) effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf10a (by decide)))
  have frameC : AgreesExcept [.flags, .rip] b c := effectC.agrees
  have stateC := stateB.after_registers readyC frameC (by simp [Component.Covers]) (by simp)
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (P256.Proofs.Common.Curve.LinearCombination.Loop.cmova_r64_r64_effect_step
      0x10f10a 0x49 0x47 0xda (by simp [RexWPrefix]) rfl rfl).advances readyC
      (programText_slice (programLoaded_codeIn stateC.loaded) 0xf10a _
        (by decide) (by decide +kernel)) effectC.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf10e (by decide)))
  have frameW : AgreesExcept [.reg 3, .rip] c w := effectW.agrees
  have frame : AgreesExcept [.reg 10, .reg 3, .flags, .rip] t w :=
    (((frameA.trans frameB).trans frameC).trans frameW).mono (by simp)
  refine ⟨w, ((runA.trans runB).trans runC).trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip, ?_, frame⟩
  have h := effectW.writes
  change w.regValue .rbx = if !((StatusFlags.ofRFLAGS c.RFLAGS).CF ||
      (StatusFlags.ofRFLAGS c.RFLAGS).ZF) then c.regValue .r10 else c.regValue .rbx at h
  have cf := effectC.flags.1
  have zf := effectC.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS c.RFLAGS).CF = decide ((b.regValue .r10).toNat < (b.regValue .rbx).toNat) at cf
  change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = (b.regValue .r10 - b.regValue .rbx == 0) at zf
  have r10C : c.regValue .r10 = b.regValue .r10 := frameC.read (n := 64) (r := 10) (by simp)
  have bxC : c.regValue .rbx = b.regValue .rbx := frameC.read (n := 64) (r := 3) (by simp)
  have maximum_value (x y : BitVec 64) :
      (if !(decide (x.toNat < y.toNat) || (x - y == 0)) then x else y) =
        BitVec.ofNat 64 (max x.toNat y.toNat) := by
    by_cases h : y.toNat < x.toNat
    · have hxy : x ≠ y := fun he => (Nat.ne_of_lt h) (congrArg BitVec.toNat he).symm
      have hsub : x - y ≠ 0#64 := by
        intro he
        exact hxy ((BitVec.sub_eq_iff_eq_add.mp he).trans (BitVec.zero_add y))
      have hm : max x.toNat y.toNat = x.toNat := Nat.max_eq_left (by omega)
      simp [show ¬x.toNat < y.toNat by omega, hsub, hm]
    · have hm : max x.toNat y.toNat = y.toNat := Nat.max_eq_right (by omega)
      by_cases he : x = y
      · subst y; simp
      · have hn : x.toNat < y.toNat := by
          have hn : x.toNat ≠ y.toNat := fun eq => he (BitVec.eq_of_toNat_eq eq)
          omega
        simp [hn, hm]
  rw [cf, zf, r10C, bxC, maximum_value, r10B, bxB] at h
  have hlu := Naf.digits_length u hu
  have hlv := Naf.digits_length v hv
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (Naf.digits u).length < 2^64 by omega),
    Nat.mod_eq_of_lt (show (Naf.digits v).length < 2^64 by omega)] using h

end P256.Proofs.Verifying.Combination.Loop.Multi
