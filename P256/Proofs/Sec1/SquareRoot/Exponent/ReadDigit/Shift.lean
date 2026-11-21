import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.State
import P256.Proofs.Sec1.SquareRoot.Exponent.Window
import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.Lea
import P256.Proofs.Common.Instructions.Lea32.NoBase
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Lea32 (leaR32NoBaseEffect)
open P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount (clCount clCount_eq_mod shr_r64_cl_effect_step)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_digit_shift [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (hn : n < 64) (hip : t.RIP = 0x11586c) :
    ∃ u, Advances boundary 3 t u ∧ ReadyToStep u ∧ u.RIP = 0x11587f ∧
      (Operand.reg 0 : Operand 64).read u =
        (BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (n / 16)))) >>> (4 * (n % 16)) ∧
      AgreesExcept digitReadComponents t u := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset offset ho)
  have hc1 : CodeIn (codeRange 0x11586c [0x42, 0x8d, 0x0c, 0xb5, 0, 0, 0, 0]) t :=
    programText_slice (programLoaded_codeIn hp.frame.loaded) 0x1586c _ (by decide) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ := (lea_ecx_r14_scale4_effect_step 0x11586c).advances
    (readyToStep hp.frame.machine hp.frame.bindingsSupported) hc1 hip (hnext 0x15874 (by decide))
  have hag1 : AgreesExcept digitReadComponents t t1 :=
    he1.agrees.mono (by simp [leaR32NoBaseEffect, Effect.components, digitReadComponents])
  have hp1 := hp.of_digit_registers hr1 hag1
  have hcount1 : (Operand.reg 1 : Operand 64).read t1 = BitVec.ofNat 64 (4 * (n % 16)) := by
    have hv := he1.writes
    change (Operand.reg 1 : Operand 64).read t1 =
      ((((Operand.reg 14 : Operand 64).read t <<< (2 : Nat)) + 0).setWidth 32).setWidth 64 at hv
    have hw : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (n % 16) := hp.window
    rw [hv, hw]
    change (((BitVec.ofNat 64 (n % 16) <<< (2 : Nat)) + 0#64).setWidth 32).setWidth 64 = _
    rw [BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have haddr : (AddrMode.sib 4 (some 5) 3 (.d32 0x538)).addr t1 0x11587c =
      exponentFrameBase s + 0x538 + BitVec.ofNat 64 (8 * (n / 16)) := by
    change t1.regValue .rsp + (t1.regValue .rbp <<< (3 : Nat)) + 0x538 = _
    rw [hp1.frame.rsp, hp1.word]
    have hshift : BitVec.ofNat 64 (n / 16) <<< (3 : Nat) = BitVec.ofNat 64 (8 * (n / 16)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    rw [hshift, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * (n / 16))) 0x538,
      ← BitVec.add_assoc]
  have hread : MemReadable t1
      ((AddrMode.sib 4 (some 5) 3 (.d32 0x538)).addr t1 0x11587c) 8 := by
    rw [haddr]
    have hh := hp1.frame.stack_readable ctx
      (offset := 0x538 + 8 * (n / 16)) (len := 8) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hh
    exact hh
  have hc2 : CodeIn (codeRange 0x115874 [0x48, 0x8b, 0x84, 0xec, 0x38, 5, 0, 0]) t1 :=
    programText_slice (programLoaded_codeIn hp1.frame.loaded) 0x15874 _ (by decide) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ := (mov_r64_m64_effect_step 0x115874 0x48
      (by constructor <;> rfl) 0 (.sib 4 (some 5) 3 (.d32 0x538))
      (by simp [AddrMode.Valid]) rfl rfl).advances hr1 hc2 ⟨he1.rip, hread⟩
      (hnext 0x1587c (by decide))
  have hs2 : AgreesExcept [.reg 0, .rip] t1 t2 := he2.agrees
  have hag2 : AgreesExcept digitReadComponents t1 t2 :=
    hs2.mono (by simp [digitReadComponents])
  have hp2 := hp1.of_digit_registers hr2 hag2
  have hword2 : (Operand.reg 0 : Operand 64).read t2 =
      BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (n / 16))) := by
    have hw := he2.writes
    change (Operand.reg 0 : Operand 64).read t2 = memLoad t1.external
      ((AddrMode.sib 4 (some 5) 3 (.d32 0x538)).addr t1 0x11587c) 64 at hw
    rw [hw, haddr, hp1.constants.load_exponent_word hn]
  have hcount2 : clCount t2 = 4 * (n % 16) := by
    rw [clCount_eq_mod]
    have hc : (Operand.reg 1 : Operand 64).read t2 = BitVec.ofNat 64 (4 * (n % 16)) :=
      (hs2.read (by decide)).trans hcount1
    change ((Operand.reg 1 : Operand 64).read t2).toNat % 64 = _
    rw [hc, BitVec.toNat_ofNat]
    omega
  have hc3 : CodeIn (codeRange 0x11587c [0x48, 0xd3, 0xe8]) t2 :=
    programText_slice (programLoaded_codeIn hp2.frame.loaded) 0x1587c _ (by decide) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ := (shr_r64_cl_effect_step 0x11587c 0x48 0xe8
      (by constructor <;> rfl) rfl rfl).advances hr2 hc3 he2.rip
      (hnext 0x1587f (by decide))
  have hs3 : AgreesExcept [.reg 0, .flags, .rip] t2 t3 := he3.agrees
  have hag3 : AgreesExcept digitReadComponents t2 t3 :=
    hs3.mono (by simp [digitReadComponents])
  refine ⟨t3, (ha1.trans ha2).trans ha3, hr3, he3.rip, ?_,
    digitReadComponents_trans (digitReadComponents_trans hag1 hag2) hag3⟩
  change (Operand.reg 0 : Operand 64).read t3 = _
  have hw := he3.writes
  change (Operand.reg 0 : Operand 64).read t3 = (Operand.reg 0 : Operand 64).read t2 >>> clCount t2 at hw
  rw [hw, hword2, hcount2]

end P256.Proofs.Sec1.SquareRoot
