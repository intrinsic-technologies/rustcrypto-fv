import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Der.Decode.Header

open X86 X86.Machine X86.UserProcess X86Proofs

theorem jcc_rel8_taken_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (disp : BitVec 8) (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (fun s => s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (fun _ => jmpEffect p 2 (disp.signExtend 64)) := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hready', heffect⟩ :=
    jcc_rel8_effect_step p cc disp s hready hcode ⟨hpre.1, fun _ => htarget⟩
  exact ⟨t, hstep, hready', jccEffect_taken hpre.2 heffect⟩

theorem jcc_rel8_not_taken_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (disp : BitVec 8) :
    StepEffect (fun s => s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (fun _ => nopEffect p 2) := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hready', heffect⟩ :=
    jcc_rel8_effect_step p cc disp s hready hcode
      ⟨hpre.1, fun h => by simp only [hpre.2, Bool.false_eq_true] at h⟩
  exact ⟨t, hstep, hready', jccEffect_not_taken hpre.2 heffect⟩

theorem jcc_rel32_taken_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (disp : BitVec 32) (htarget : (branchTarget p 6 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (fun s => s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
      (codeRange p (0x0f :: jccOpcode32 cc :: immBytes 32 disp))
      (fun _ => jmpEffect p 6 (disp.signExtend 64)) := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hready', heffect⟩ :=
    jcc_rel32_effect_step p cc disp s hready hcode ⟨hpre.1, fun _ => htarget⟩
  exact ⟨t, hstep, hready', jccEffect_taken hpre.2 heffect⟩

theorem jcc_rel32_not_taken_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (disp : BitVec 32) :
    StepEffect (fun s => s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
      (codeRange p (0x0f :: jccOpcode32 cc :: immBytes 32 disp))
      (fun _ => nopEffect p 6) := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hready', heffect⟩ :=
    jcc_rel32_effect_step p cc disp s hready hcode
      ⟨hpre.1, fun h => by simp only [hpre.2, Bool.false_eq_true] at h⟩
  exact ⟨t, hstep, hready', jccEffect_not_taken hpre.2 heffect⟩

end P256.Proofs.Common.Der.Decode.Header
