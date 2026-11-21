import Sha3.Proofs.X86.Instructions.Cmp.Triple
import X86Proofs.Instructions.Branch.Triple
import Sha3.Proofs.Run

namespace Sha3.Proofs.Update.Tail

open X86 X86.Machine X86.UserProcess X86Proofs

theorem compare_register_branch [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (dst src : BitVec 3) (disp : BitVec 8) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s) (hip : s.RIP = p)
    (hcmpCode : ∀ byte ∈ codeRange p [0x48, 0x39, UInt8.ofNat (0xc0 + 8 * src.toNat + dst.toNat)], byte ∈ code)
    (hjmpCode : ∀ byte ∈ codeRange (p + 3#64) (0x75 :: immBytes 8 disp), byte ∈ code)
    (htarget : (branchTarget (p + 3#64) 2 (disp.signExtend 64)).toNat < 2 ^ 32)
    (hne₁ : p + 3#64 ≠ boundary.rip) (hne₂ : p + 5#64 ≠ boundary.rip)
    (hne₃ : branchTarget (p + 3#64) 2 (disp.signExtend 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg (dst.setWidth 5) : Operand 64).read s -
          (Operand.reg (src.setWidth 5) : Operand 64).read s == 0#64) then p + 5#64
        else branchTarget (p + 3#64) 2 (disp.signExtend 64)) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hcmp : StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0x39, UInt8.ofNat (0xc0 + 8 * src.toNat + dst.toNat)])
      (cmpR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
    have hdecode : ∀ d r : BitVec 3,
        modrmMod (UInt8.ofNat (0xc0 + 8 * r.toNat + d.toNat)) = 3 ∧
        gprNumber 0 (rexB (0x48 : UInt8).toBitVec)
          (modrmRm (UInt8.ofNat (0xc0 + 8 * r.toNat + d.toNat))) = d.setWidth 5 ∧
        gprNumber 0 (rexR (0x48 : UInt8).toBitVec)
          (modrmReg (UInt8.ofNat (0xc0 + 8 * r.toNat + d.toNat))) = r.setWidth 5 := by decide +kernel
    have h := cmp_r64_r64_effect_step p 0x48 (UInt8.ofNat (0xc0 + 8 * src.toNat + dst.toNat))
      (by unfold RexWPrefix; decide) (hdecode dst src).1
    simpa only [(hdecode dst src).2.1, (hdecode dst src).2.2] using h
  obtain ⟨u, hrun₁, hready₁, hu⟩ := hcmp.advances hready (hcode.mono hcmpCode) hip hne₁
  have hc₁ : CodeIn code u := hu.codeIn (cmpR64R64Effect_avoids p (dst.setWidth 5) (src.setWidth 5) s code) hcode
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Operand.reg (dst.setWidth 5) : Operand 64).read s - (Operand.reg (src.setWidth 5) : Operand 64).read s == 0#64) :=
    hu.flags.2.2.2.1
  have hcc : condHolds 5#4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      Bool.not ((Operand.reg (dst.setWidth 5) : Operand 64).read s -
        (Operand.reg (src.setWidth 5) : Operand 64).read s == 0#64) := by
    change Bool.not (StatusFlags.ofRFLAGS u.RFLAGS).ZF = _
    exact congrArg Bool.not hz
  have hnext : p + 3#64 + BitVec.ofNat 64 2 = p + 5#64 := by
    rw [BitVec.add_assoc]
    rfl
  have hbranch := jcc_rel8_effect_step (p + 3#64) 5#4 disp
  obtain ⟨t, hrun₂, hready₂, ht⟩ := hbranch.advances hready₁ (hc₁.mono hjmpCode)
    ⟨hu.rip, fun _ ↦ htarget⟩ (by
      dsimp only [jccEffect, branchEffect]
      split
      · exact hne₃
      · exact hnext ▸ hne₂)
  refine ⟨t, hrun₁.trans hrun₂, hready₂,
    ht.codeIn (branchEffect_avoids _ _ _ code) hc₁, ?_, ?_⟩
  · have hip' := ht.rip
    simp only [jccEffect, branchEffect, hcc, hnext] at hip'
    cases he : ((Operand.reg (dst.setWidth 5) : Operand 64).read s -
      (Operand.reg (src.setWidth 5) : Operand 64).read s == 0#64) <;> rw [he] at hip' <;> exact hip'
  · apply (hu.agrees.trans ht.agrees).mono
    simp only [cmpR64R64Effect_components, jccEffect, branchEffect_components]
    intro c hc
    simpa using hc


theorem compare_branch [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (disp : BitVec 8) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s) (hip : s.RIP = p)
    (hcmpCode : ∀ byte ∈ codeRange p [0x48, 0x39, 0xd0], byte ∈ code)
    (hjmpCode : ∀ byte ∈ codeRange (p + 3#64) (0x75 :: immBytes 8 disp), byte ∈ code)
    (htarget : (branchTarget (p + 3#64) 2 (disp.signExtend 64)).toNat < 2 ^ 32)
    (hne₁ : p + 3#64 ≠ boundary.rip) (hne₂ : p + 5#64 ≠ boundary.rip)
    (hne₃ : branchTarget (p + 3#64) 2 (disp.signExtend 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg 0#5 : Operand 64).read s -
          (Operand.reg 2#5 : Operand 64).read s == 0#64) then p + 5#64
        else branchTarget (p + 3#64) 2 (disp.signExtend 64)) ∧
      AgreesExcept [.flags, .rip] s t :=
  compare_register_branch boundary code p 0#3 2#3 disp s hready hcode hip hcmpCode hjmpCode
    htarget hne₁ hne₂ hne₃



theorem sub_ofNat_beq_zero {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (BitVec.ofNat n a - BitVec.ofNat n b == 0#n) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h'
  · exact congrArg (BitVec.ofNat n)

end Sha3.Proofs.Update.Tail
