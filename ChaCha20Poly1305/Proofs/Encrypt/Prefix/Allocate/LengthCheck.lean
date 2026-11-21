import ChaCha20Poly1305.Proofs.Wrapper
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def lengthChanges : List Component := [.reg 5, .flags, .rip]

set_option maxHeartbeats 600000 in
theorem check_length [Bindings] {s : RamState} {n : Nat}
    {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack lengthChanges s s) (rip : s.RIP = 0x101808)
    (len : rd s 13 = BitVec.ofNat 64 n) (bound : n < 2^32) :
    ∃ t, Advances boundary 5 s t ∧ GTrack lengthChanges s t ∧
      t.RIP = (if n = 0 then 0x101828 else 0x101819) ∧ rd t 5 = 0 := by
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (cmp_r64_imm8_effect_step 0x101808 0x49 0xfd 0xf0
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x1808 4 (by decide +kernel)) rip
    (code_ne_boundary outside 0x180c (by omega))
    (by simp only [cmpR64Imm8Effect_components]; fits [lengthChanges])
  change (cmpR64Imm8Effect 0x101808 13 0xf0 s).Holds s u1 at e1
  have cf : (StatusFlags.ofRFLAGS u1.RFLAGS).CF = true := by
    have h := e1.flags
    simp only [Effect.FlagsHold, cmpR64Imm8Effect] at h
    have hcf := h.1
    change (StatusFlags.ofRFLAGS u1.RFLAGS).CF = (cmpSpec (rd s 13) _).CF at hcf
    rw [hcf, len]
    change decide ((BitVec.ofNat 64 n).toNat < 18446744073709551600) = true
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
    omega
  have hz : condHolds 3 (StatusFlags.ofRFLAGS u1.RFLAGS) = false := by
    change (!(StatusFlags.ofRFLAGS u1.RFLAGS).CF) = false
    rw [cf]; rfl
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (jcc_rel32_effect_step 0x10180c 3 0xde)
    T1 (program_text_slice T1.code 0x180c 6 (by decide +kernel))
    ⟨e1.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hz]
        exact code_ne_boundary outside 0x1812 (by omega))
    (by fits [lengthChanges])
  have rip2 : u2.RIP = 0x101812 := (jccEffect_not_taken hz e2).rip
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (xor_r32_r32_effect_step 0x101812 0xed (by decide))
    T2 (program_text_slice T2.code 0x1812 2 (by decide +kernel)) rip2
    (code_ne_boundary outside 0x1814 (by omega)) (by fits [lengthChanges])
  change (xorR32R32Effect 0x101812 2 5 5 u2).Holds u2 u3 at e3
  have zero : rd u3 5 = 0 := by
    rw [show rd u3 5 = _ from e3.writes]
    simp
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (test_r64_r64_effect_step 0x101814 0x4d 0xed (by unfold RexWPrefix; decide) (by decide))
    T3 (program_text_slice T3.code 0x1814 3 (by decide +kernel)) e3.rip
    (code_ne_boundary outside 0x1817 (by omega))
    (by simp only [testR64R64Effect_components]; fits [lengthChanges])
  change (testR64R64Effect 0x101814 13 13 u3).Holds u3 u4 at e4
  have zf : condHolds 4 (StatusFlags.ofRFLAGS u4.RFLAGS) = decide (n = 0) := by
    have hf := e4.flags
    simp only [Effect.FlagsHold, testR64R64Effect] at hf
    have h := hf.2.2.2.1
    change (StatusFlags.ofRFLAGS u4.RFLAGS).ZF = _ at h
    rw [condHolds_4, h]
    have len3 : rd u3 13 = BitVec.ofNat 64 n := (T3.agrees.read (by simp [lengthChanges])).trans len
    change ((rd u3 13 &&& rd u3 13) == 0) = decide (n = 0)
    rw [len3, BitVec.and_self]
    have hn : n < 2^64 := by omega
    by_cases hz : n = 0
    · subst n; rfl
    · have hv : BitVec.ofNat 64 n ≠ 0 := by
        intro he
        have := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
        exact hz this
      simp only [hz, decide_false, beq_eq_false_iff_ne]
      exact hv
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step (jcc_rel8_effect_step 0x101817 4 0xf)
    T4 (program_text_slice T4.code 0x1817 2 (by decide +kernel))
    ⟨e4.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, zf]; split
        · exact code_ne_boundary outside 0x1828 (by omega)
        · exact code_ne_boundary outside 0x1819 (by omega))
    (by fits [lengthChanges])
  refine ⟨u5, a1.trans (a2.trans (a3.trans (a4.trans a5))), T5, ?_, ?_⟩
  · have ht : branchTarget 0x101817 2 ((0xf : BitVec 8).signExtend 64) = 0x101828 := by decide
    have h := e5.rip
    simp only [jccEffect, branchEffect, zf, decide_eq_true_eq, ht] at h
    exact h.trans (by split <;> rfl)
  · exact (e5.agrees.read (by simp [jccEffect])).trans
      ((e4.agrees.read (by simp)).trans zero)

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
