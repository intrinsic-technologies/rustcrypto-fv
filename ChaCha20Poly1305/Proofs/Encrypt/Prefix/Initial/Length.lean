import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

theorem length_check [Bindings] {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (outside : ¬ InProgram boundary.rip) (hn : n < 2^32)
    (track : GTrack [.reg 5, .flags, .rip] s s)
    (entry : s.RIP = 0x10179d) (length : rd s 13 = BitVec.ofNat 64 n) :
    ∃ t, Advances boundary 3 s t ∧ GTrack [.reg 5, .flags, .rip] s t ∧
      t.RIP = 0x1017aa ∧ rd t 5 = BitVec.ofNat 64 (n + 16) ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).ZF = false := by
  obtain ⟨u, a1, T1, e1⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x10179d 0x4c 0xed
      (by unfold RexWPrefix; decide) (by decide))
    track (program_text_slice track.code 0x179d 3 (by decide +kernel)) entry
    (code_ne_boundary outside 0x17a0 (by omega)) (by fits [])
  change (movR64R64Effect 0x10179d 5 13 s).Holds s u at e1
  have r1 : rd u 5 = BitVec.ofNat 64 n := e1.writes.trans length
  obtain ⟨v, a2, T2, e2⟩ := gtrack_step
    (add_r64_imm8_effect_step 0x1017a0 0x48 0xc5 0x10
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    T1 (program_text_slice T1.code 0x17a0 4 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x17a4 (by omega)) (by fits [])
  change (addR64Imm8Effect 0x1017a0 5 0x10 u).Holds u v at e2
  have r2 : rd v 5 = BitVec.ofNat 64 (n + 16) := by
    have h : rd v 5 = rd u 5 + 16#64 := e2.writes
    rw [h, r1, BitVec.ofNat_add]
  have sf : (StatusFlags.ofRFLAGS v.RFLAGS).SF = false := by
    have h := e2.flags.2.2.2.2.1
    change (StatusFlags.ofRFLAGS v.RFLAGS).SF = (addSpec (rd u 5) 16#64).2.SF at h
    rw [h, r1]
    simp only [addSpec, BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not]
    omega
  have zf : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = false := by
    have h := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF = (addSpec (rd u 5) 16#64).2.ZF at h
    rw [h, r1]
    simp only [addSpec, beq_eq_false_iff_ne]
    intro he
    have ht := congrArg BitVec.toNat he
    change (n % 2^64 + 16) % 2^64 = 0 at ht
    omega
  have cond : condHolds 8 (StatusFlags.ofRFLAGS v.RFLAGS) = false := by
    exact (condHolds_8 _).trans sf
  obtain ⟨t, a3, T3, e3⟩ := gtrack_step (jcc_rel32_effect_step 0x1017a4 8 0x174)
    T2 (program_text_slice T2.code 0x17a4 6 (by decide +kernel))
    ⟨e2.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, cond, Bool.false_eq_true, ↓reduceIte]
        exact code_ne_boundary outside 0x17aa (by omega))
    (by fits [])
  refine ⟨t, a1.trans (a2.trans a3), T3, (jccEffect_not_taken cond e3).rip, ?_, ?_⟩
  · exact (e3.agrees.read (by simp [jccEffect])).trans r2
  · rw [flags_keep e3.agrees (by simp [jccEffect])]
    exact zf

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
