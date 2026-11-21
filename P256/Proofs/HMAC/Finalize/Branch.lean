import P256.Proofs.Program.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem padding_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (ready : ReadyToStep s)
    (code : CodeIn (codeRange p [0x49,0x83,modrm,7,0x0f,0x87,0xa4,0,0,0]) s)
    (rip : s.RIP = p)
    (large : 8 ≤ ((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read s).toNat)
    (next : p + 4#64 ≠ boundary.rip)
    (target : p + 174#64 ≠ boundary.rip)
    (bound : (p + 174#64).toNat < 2^32) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = p + 174#64 ∧ AgreesExcept [.flags,.rip] s t := by
  obtain ⟨u, run, readyU, compare⟩ :=
    (cmp_r64_imm8_effect_step p 0x49 modrm 7#8
      (by simp [RexWPrefix]) hmod hreg).advances ready
      (code.mono (by simpa only [BitVec.add_zero, immBytes_eight, List.drop_zero, List.take_succ_cons, List.take_zero, show UInt8.ofBitVec 7#8 = (7 : UInt8) by decide +kernel] using codeRange_slice_subset p [0x49,0x83,modrm,7,0x0f,0x87,0xa4,0,0,0] 0 4)) rip next
  have frame : AgreesExcept [.flags,.rip] s u := compare.agrees
  have branchCode : CodeIn (codeRange (p + 4#64) [0x0f,0x87,0xa4,0,0,0]) u :=
    (frame.codeIn (by simp [Component.Covers]) code).mono
      (codeRange_slice_subset p [0x49,0x83,modrm,7,0x0f,0x87,0xa4,0,0,0] 4 6)
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel32_effect_step (p + 4#64) 7 0xa4 u readyU
    branchCode ⟨compare.rip, by intro _; simpa only [branchTarget, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using bound⟩
  · have carry := compare.flags.1
    have zero := compare.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      ((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read s).ult 7 at carry
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read s) - 7 == 0) at zero
    have cf : (StatusFlags.ofRFLAGS u.RFLAGS).CF = false := by
      rw [carry, BitVec.ult_eq_decide]
      simp only [decide_eq_false_iff_not, BitVec.reduceToNat]
      omega
    have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
      rw [zero]
      apply Bool.eq_false_iff.mpr
      intro eq
      have eq' := beq_iff_eq.mp eq
      have same : ((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read s) = 7#64 := by
        simpa only [BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd] using eq'
      have natSame := congrArg BitVec.toNat same
      change _ = 7 at natSame
      omega
    have targetRip : t.RIP = p + 174#64 := by
      rw [branch.rip]
      change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
        then p + 4#64 + 6#64 + 164#64 else p + 4#64 + 6#64) = _
      simp only [cf, zf, Bool.false_or, Bool.not_false, ite_true,
        BitVec.add_assoc, BitVec.reduceAdd]
    refine ⟨t, run.trans (Advances.of_step step (.inl (targetRip ▸ target))),
      readyT, targetRip, ?_⟩
    exact (frame.trans branch.agrees).mono
      (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])

end P256.Proofs.HMAC.Finalize
