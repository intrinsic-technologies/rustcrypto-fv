import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.Shift
import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.Mask
import X86Proofs.Instructions.And.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_read_digit [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (hn : n < 64) (hip : t.RIP = 0x11586c) :
    ∃ u, Advances boundary 11 t u ∧ ExponentPosition s u x n ∧
      u.RIP = (if sqrtExponent / 16 ^ n % 16 = 0 then 0x1154c0 else 0x1158a2) ∧
      (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 (sqrtExponent / 16 ^ n % 16) ∧
      u.external = t.external := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset offset ho)
  obtain ⟨t1, ha1, hr1, hi1, hv1, hag1⟩ := exponent_digit_shift ctx hp hn hip
  have hp1 := hp.of_digit_registers hr1 hag1
  obtain ⟨t2, ha2, hr2, hi2, hv2, hag2⟩ := exponent_digit_mask ctx hp1 hn hi1
  have hag2' : AgreesExcept digitReadComponents t1 t2 :=
    hag2.mono (by simp [digitReadComponents])
  have hp2 := hp1.of_digit_registers hr2 hag2'
  have hax2 : (Operand.reg 0 : Operand 32).read t2 =
      ((BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (n / 16)))) >>> (4 * (n % 16))).setWidth 32 := by
    have hh : (Operand.reg 0 : Operand 64).read t2 = _ :=
      (hag2.read (n := 64) (r := 0) (by decide)).trans hv1
    exact congrArg (BitVec.setWidth 32) hh
  have hcx2 : (Operand.reg 1 : Operand 32).read t2 =
      ((if n = 63 then 3 else 15) : BitVec 32) := by
    have hh := congrArg (BitVec.setWidth 32) hv2
    by_cases he : n = 63
    · rw [ite_eq_left he] at hh ⊢
      exact hh
    · rw [ite_eq_right he] at hh ⊢
      exact hh
  have hand : ((Operand.reg 0 : Operand 32).read t2 &&& (Operand.reg 1 : Operand 32).read t2) =
      BitVec.ofNat 32 (sqrtExponent / 16 ^ n % 16) := by
    rw [hax2, hcx2]
    exact sqrtExponent_digit n hn
  have hc3 : CodeIn (codeRange 0x11589a [0x21, 0xc8]) t2 :=
    programText_slice (programLoaded_codeIn hp2.frame.loaded) 0x1589a _ (by decide) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ := (and_r32_r32_effect_step 0x11589a 0xc8 rfl).advances
    hr2 hc3 hi2 (hnext 0x1589c (by decide))
  have hs3 : AgreesExcept [.reg 0, .flags, .rip] t2 t3 := he3.agrees
  have hag3 : AgreesExcept digitReadComponents t2 t3 := hs3.mono (by simp [digitReadComponents])
  have hp3 := hp2.of_digit_registers hr3 hag3
  have hv3 : (Operand.reg 0 : Operand 64).read t3 =
      BitVec.ofNat 64 (sqrtExponent / 16 ^ n % 16) := by
    have hh := he3.writes
    change (Operand.reg 0 : Operand 64).read t3 =
      ((Operand.reg 0 : Operand 32).read t2 &&& (Operand.reg 1 : Operand 32).read t2).setWidth 64 at hh
    rw [hh, hand]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  have hf3 : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = decide (sqrtExponent / 16 ^ n % 16 = 0) := by
    have hh := he3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t3.RFLAGS).ZF =
      (((Operand.reg 0 : Operand 32).read t2 &&& (Operand.reg 1 : Operand 32).read t2) == 0) at hh
    rw [hh, hand]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro he
      have he' := congrArg BitVec.toNat he
      change (sqrtExponent / 16 ^ n % 16) % 4294967296 = 0 at he'
      omega
    · intro he
      rw [he]
      rfl
  have hc4 : CodeIn (codeRange 0x11589c [0x0f, 0x84, 0x1e, 0xfc, 0xff, 0xff]) t3 :=
    programText_slice (programLoaded_codeIn hp3.frame.loaded) 0x1589c _ (by decide) (by decide +kernel)
  obtain ⟨t4, hm4, hr4, he4⟩ := jcc_rel32_effect_step 0x11589c 4 0xfffffc1e t3 hr3 hc4
    ⟨he3.rip, fun _ => by decide⟩
  have hs4 : AgreesExcept [.rip] t3 t4 := he4.agrees
  have hi4 : t4.RIP = (if sqrtExponent / 16 ^ n % 16 = 0 then 0x1154c0 else 0x1158a2) := by
    rw [he4.rip]
    change (if (StatusFlags.ofRFLAGS t3.RFLAGS).ZF then (0x1154c0 : BitVec 64) else 0x1158a2) = _
    rw [hf3]
    simp only [decide_eq_true_eq]
  have ha4 : Advances boundary 1 t3 t4 := by
    apply Advances.of_step hm4
    left
    rw [hi4]
    split
    · exact hnext 0x154c0 (by decide)
    · exact hnext 0x158a2 (by decide)
  have hag4 : AgreesExcept digitReadComponents t3 t4 := hs4.mono (by simp [digitReadComponents])
  have hall := digitReadComponents_trans (digitReadComponents_trans
    (digitReadComponents_trans hag1 hag2') hag3) hag4
  exact ⟨t4, ((ha1.trans ha2).trans ha3).trans ha4, hp3.of_digit_registers hr4 hag4,
    hi4, (hs4.read (by decide)).trans hv3, hall.external (by simp [digitReadComponents, Component.Covers])⟩

end P256.Proofs.Sec1.SquareRoot
