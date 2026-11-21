import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.MemoryContracts
import X86Proofs.Instructions.Test.Generated.R8.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper CoreContract MemoryRoutines.Machine

def outputTailChanges : List Component :=
  [.reg 4, .flags, .rip, .reg 3, .reg 12, .reg 13, .reg 14, .reg 15, .reg 5]

theorem output_tail [Machine.Bindings] {initial v : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip)
    (hLow : (returnBoundary initial).rip.toNat < 2 ^ 32)
    (T0 : GTrack outputTailChanges v v) (hrip : v.RIP = 0x1018c7)
    (hsp : stackPtr v = stackPtr initial - BitVec.ofNat 64 168)
    (hP : RetPresent (stackPtr initial) v)
    (hret : wd v (stackPtr initial) = (returnBoundary initial).rip) :
    ∃ n fin, Returns (returnBoundary initial) n v fin ∧ ReadyToStep fin ∧
      AgreesExcept outputTailChanges v fin ∧
      rd fin 3 = wd v (stackPtr initial - BitVec.ofNat 64 48) ∧
      rd fin 12 = wd v (stackPtr initial - BitVec.ofNat 64 40) ∧
      rd fin 13 = wd v (stackPtr initial - BitVec.ofNat 64 32) ∧
      rd fin 14 = wd v (stackPtr initial - BitVec.ofNat 64 24) ∧
      rd fin 15 = wd v (stackPtr initial - BitVec.ofNat 64 16) ∧
      rd fin 5 = wd v (stackPtr initial - BitVec.ofNat 64 8) := by
  have hroom := hS.room
  have htop := hS.top
  obtain ⟨w1, a1, T1, e1⟩ := gtrack_step
    (add_r64_imm8_effect_step 0x1018c7 0x48 0xc4 0x78 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    T0 (program_text_slice T0.code 0x18c7 4 (by decide +kernel))
    hrip (code_ne_boundary hOut 0x18cb (by omega)) (by fits [outputTailChanges])
  change (addR64Imm8Effect 0x1018c7 4 0x78 v).Holds v w1 at e1
  have hsp1 : stackPtr w1 = stackPtr initial - BitVec.ofNat 64 48 := by
    rw [stackPtr_eq_read, show (Operand.reg 4 : Operand 64).read w1 = _ from e1.writes,
      ← stackPtr_eq_read, hsp, show (0x78 : BitVec 8).signExtend 64 = BitVec.ofNat 64 120 from by
        decide]
    rw [show (168 : Nat) = 48 + 120 from rfl, ← sub_sub_ofNat, BitVec.sub_add_cancel]
  obtain ⟨w2, a2, T2, e2⟩ := gtrack_step
    (pop_r64_effect_step 0x1018cb 0x5b (by decide) (by decide))
    T1 (program_text_slice T1.code 0x18cb 1 (by decide +kernel))
    ⟨e1.rip, by rw [hsp1]; exact ret_readable hroom htop (hP.of_agrees T1.agrees) (k := 48) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18cc (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018cb 1 3 w1).Holds w1 w2 at e2
  have hsp2 : stackPtr w2 = stackPtr initial - BitVec.ofNat 64 40 := by
    have h := e2.writes.2
    change stackPtr w2 = stackPtr w1 + BitVec.ofNat 64 8 at h
    rw [h, hsp1]; bv_omega
  obtain ⟨w3, a3, T3, e3⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1018cc 0x41 0x5c (by unfold RexPrefix; decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x18cc 2 (by decide +kernel))
    ⟨e2.rip, by rw [hsp2]; exact ret_readable hroom htop (hP.of_agrees T2.agrees) (k := 40) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18ce (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018cc 2 12 w2).Holds w2 w3 at e3
  have hsp3 : stackPtr w3 = stackPtr initial - BitVec.ofNat 64 32 := by
    have h := e3.writes.2
    change stackPtr w3 = stackPtr w2 + BitVec.ofNat 64 8 at h
    rw [h, hsp2]; bv_omega
  obtain ⟨w4, a4, T4, e4⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1018ce 0x41 0x5d (by unfold RexPrefix; decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x18ce 2 (by decide +kernel))
    ⟨e3.rip, by rw [hsp3]; exact ret_readable hroom htop (hP.of_agrees T3.agrees) (k := 32) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18d0 (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018ce 2 13 w3).Holds w3 w4 at e4
  have hsp4 : stackPtr w4 = stackPtr initial - BitVec.ofNat 64 24 := by
    have h := e4.writes.2
    change stackPtr w4 = stackPtr w3 + BitVec.ofNat 64 8 at h
    rw [h, hsp3]; bv_omega
  obtain ⟨w5, a5, T5, e5⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1018d0 0x41 0x5e (by unfold RexPrefix; decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x18d0 2 (by decide +kernel))
    ⟨e4.rip, by rw [hsp4]; exact ret_readable hroom htop (hP.of_agrees T4.agrees) (k := 24) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18d2 (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018d0 2 14 w4).Holds w4 w5 at e5
  have hsp5 : stackPtr w5 = stackPtr initial - BitVec.ofNat 64 16 := by
    have h := e5.writes.2
    change stackPtr w5 = stackPtr w4 + BitVec.ofNat 64 8 at h
    rw [h, hsp4]; bv_omega
  obtain ⟨w6, a6, T6, e6⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1018d2 0x41 0x5f (by unfold RexPrefix; decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x18d2 2 (by decide +kernel))
    ⟨e5.rip, by rw [hsp5]; exact ret_readable hroom htop (hP.of_agrees T5.agrees) (k := 16) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18d4 (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018d2 2 15 w5).Holds w5 w6 at e6
  have hsp6 : stackPtr w6 = stackPtr initial - BitVec.ofNat 64 8 := by
    have h := e6.writes.2
    change stackPtr w6 = stackPtr w5 + BitVec.ofNat 64 8 at h
    rw [h, hsp5]; bv_omega
  obtain ⟨w7, a7, T7, e7⟩ := gtrack_step
    (pop_r64_effect_step 0x1018d4 0x5d (by decide) (by decide))
    T6 (program_text_slice T6.code 0x18d4 1 (by decide +kernel))
    ⟨e6.rip, by rw [hsp6]; exact ret_readable hroom htop (hP.of_agrees T6.agrees) (k := 8) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x18d5 (by omega)) (by fits [outputTailChanges])
  change (popR64Effect 0x1018d4 1 5 w6).Holds w6 w7 at e7
  have hsp7 : stackPtr w7 = stackPtr initial - BitVec.ofNat 64 0 := by
    have h := e7.writes.2
    change stackPtr w7 = stackPtr w6 + BitVec.ofNat 64 8 at h
    rw [h, hsp6]; bv_omega
  have hmem : ∀ a, wd w7 a = wd v a :=
    mem_keep T7.agrees (by simp [outputTailChanges, Component.isMem])
  have hP7 := hP.of_agrees T7.agrees
  obtain ⟨fin, hstep, hready, e8⟩ := ret_effect_step 0x1018d5 w7 T7.ready
    (program_text_slice T7.code 0x18d5 1 (by decide +kernel))
    ⟨⟨e7.rip, by
        rw [hsp7]
        have := ret_readable hroom htop hP7 (k := 0) (n := 8) (by omega) (by omega)
        simpa using this⟩,
      by
        change (wd w7 (stackPtr w7)).toNat < 2 ^ 32
        rw [hsp7, BitVec.sub_zero, hmem, hret]; exact hLow⟩
  change (retEffect w7).Holds w7 fin at e8
  have hRet : Returns (returnBoundary initial) 1 w7 fin := by
    apply Returns.of_step hstep
    · rw [e8.rip]
      change wd w7 (stackPtr w7) = _
      rw [hsp7, BitVec.sub_zero, hmem, hret]
    · exact (show (Operand.reg 4 : Operand 64).read fin = stackPtr w7 + 8 from e8.writes).trans
        (by rw [hsp7, BitVec.sub_zero]; rfl)
  refine ⟨_, fin, (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))).returns hRet, hready,
    (T7.agrees.trans e8.agrees).mono (by
      intro c hc
      simp only [List.mem_append, retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact hc
      all_goals simp [outputTailChanges]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := e2.writes.1
    change rd w2 3 = wd w1 (stackPtr w1) at h
    rw [hsp1] at h
    exact ((e3.agrees.trans (e4.agrees.trans (e5.agrees.trans (e6.agrees.trans (e7.agrees.trans e8.agrees))))).read (by simp)).trans
      (h.trans (mem_keep T1.agrees (by simp [outputTailChanges, Component.isMem]) _))
  · have h := e3.writes.1
    change rd w3 12 = wd w2 (stackPtr w2) at h
    rw [hsp2] at h
    exact ((e4.agrees.trans (e5.agrees.trans (e6.agrees.trans (e7.agrees.trans e8.agrees)))).read (by simp)).trans
      (h.trans (mem_keep T2.agrees (by simp [outputTailChanges, Component.isMem]) _))
  · have h := e4.writes.1
    change rd w4 13 = wd w3 (stackPtr w3) at h
    rw [hsp3] at h
    exact ((e5.agrees.trans (e6.agrees.trans (e7.agrees.trans e8.agrees))).read (by simp)).trans
      (h.trans (mem_keep T3.agrees (by simp [outputTailChanges, Component.isMem]) _))
  · have h := e5.writes.1
    change rd w5 14 = wd w4 (stackPtr w4) at h
    rw [hsp4] at h
    exact ((e6.agrees.trans (e7.agrees.trans e8.agrees)).read (by simp)).trans
      (h.trans (mem_keep T4.agrees (by simp [outputTailChanges, Component.isMem]) _))
  · have h := e6.writes.1
    change rd w6 15 = wd w5 (stackPtr w5) at h
    rw [hsp5] at h
    exact ((e7.agrees.trans e8.agrees).read (by simp)).trans
      (h.trans (mem_keep T5.agrees (by simp [outputTailChanges, Component.isMem]) _))
  · have h := e7.writes.1
    change rd w7 5 = wd w6 (stackPtr w6) at h
    rw [hsp6] at h
    exact (e8.agrees.read (by simp)).trans
      (h.trans (mem_keep T6.agrees (by simp [outputTailChanges, Component.isMem]) _))


theorem output_success [Bindings] {v : RamState} {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    (T0 : GTrack [.reg 0, .flags, .rip] v v) (hrip : v.RIP = 0x1018be) :
    ∃ w, Advances boundary 2 v w ∧ GTrack [.reg 0, .flags, .rip] v w ∧
      w.RIP = 0x1018c7 ∧ rd w 0 = 0 := by
  obtain ⟨w1, a1, T1, e1⟩ := gtrack_step
    (xor_r32_r32_effect_step 0x1018be 0xc0 (by decide))
    T0 (program_text_slice T0.code 0x18be 2 (by decide +kernel))
    hrip (code_ne_boundary hOut 0x18c0 (by omega)) (by fits [jmpEffect_components])
  change (xorR32R32Effect 0x1018be 2 0 0 v).Holds v w1 at e1
  have hz : rd w1 0 = 0 := by
    rw [show rd w1 0 = _ from e1.writes]
    simp
  obtain ⟨w2, a2, T2, e2⟩ := gtrack_step
    (jmp_rel8_effect_step 0x1018c0 0x05 (by decide))
    T1 (program_text_slice T1.code 0x18c0 2 (by decide +kernel))
    e1.rip (code_ne_boundary hOut 0x18c7 (by omega)) (by fits [jmpEffect_components])
  exact ⟨w2, a1.trans a2, T2, e2.rip, (e2.agrees.read (by simp)).trans hz⟩

def outputPrepChanges : List Component := [.reg 0, .reg 2, .reg 6, .reg 7, .flags, .rip]

theorem output_prepare [Bindings] {v : RamState} {boundary : ReturnBoundary}
    {I heap len cap out : BitVec 64}
    (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack outputPrepChanges v v) (hrip : v.RIP = 0x101893)
    (hsp : stackPtr v = I - 168) (hzero : rd v 0 = 0) (hout : rd v 3 = out)
    (hread : ∀ d ∈ [0, 8, 16, 200], MemReadable v (I - 168 + BitVec.ofNat 64 d) 8)
    (hcap : wd v (I - 168) ≠ -1)
    (hlen : wd v (I - 152) = len) (hheap : wd v (I - 160) = heap)
    (houtcap : wd v (I + 32) = cap) (hroom : len.toNat ≤ cap.toNat) :
    ∃ w, Advances boundary 10 v w ∧ GTrack outputPrepChanges v w ∧
      w.RIP = 0x1018b8 ∧ stackPtr w = I - 168 ∧
      rd w 7 = out ∧ rd w 6 = heap ∧ rd w 2 = len := by
  have reads {u : RamState} (T : GTrack outputPrepChanges v u) (d : Nat)
      (hd : d ∈ [0, 8, 16, 200]) : MemReadable u (I - 168 + BitVec.ofNat 64 d) 8 :=
    ⟨(hread d hd).low, fun i hi => T.agrees.grow _ ((hread d hd).mem i hi)⟩
  have memory {u : RamState} (T : GTrack outputPrepChanges v u) :
      ∀ a, wd u a = wd v a := mem_keep T.agrees (by simp [outputPrepChanges, Component.isMem])
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (test_r8_r8_effect_step 0x101893 0xc0 (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x1893 2 (by decide +kernel))
    hrip (code_ne_boundary outside 0x1895 (by omega))
    (by fits [outputPrepChanges, testR8R8Effect_components])
  change (testR8R8Effect 0x101893 2 0 0 v).Holds v u1 at e1
  have hz1 : condHolds 5 (StatusFlags.ofRFLAGS u1.RFLAGS) = false := by
    obtain ⟨-, -, -, hz, -⟩ := e1.flags
    have hal : (Operand.reg 0 : Operand 8).read v = 0 := by
      change (rd v 0).setWidth 8 = 0
      rw [hzero]; rfl
    simp only [testFlags, FlagAllows, hal] at hz
    rw [condHolds_5, hz]; rfl
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (jcc_rel8_effect_step 0x101895 5 0x2b)
    T1 (program_text_slice T1.code 0x1895 2 (by decide +kernel))
    ⟨e1.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hz1]; exact code_ne_boundary outside 0x1897 (by omega))
    (by fits [outputPrepChanges])
  have rip2 : u2.RIP = 0x101897 := (jccEffect_not_taken hz1 e2).rip
  have sp2 : stackPtr u2 = I - 168 := sp_keep T2.agrees (by simp [outputPrepChanges]) hsp
  have addr2 : ∀ x, (AddrMode.sib 4 none 0 .none).addr u2 x = I - 168 := rsp_addr0 sp2
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (cmp_m64_imm8_effect_step 0x101897 0x48 (by unfold RexWPrefix; decide)
      (AddrMode.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0xff)
    T2 (program_text_slice T2.code 0x1897 5 (by decide +kernel))
    ⟨rip2, by rw [addr2]; simpa using reads T2 0 (by simp)⟩
    (code_ne_boundary outside 0x189c (by omega))
    (by fits [outputPrepChanges, cmpMImm8Effect_components])
  change (cmpMImm8Effect 0x101897 5 64 (AddrMode.sib 4 none 0 .none) 0xff u2).Holds u2 u3 at e3
  have hz3 : condHolds 4 (StatusFlags.ofRFLAGS u3.RFLAGS) = false := by
    have hf := e3.flags
    simp only [Effect.FlagsHold, cmpMImm8Effect, addr2] at hf
    obtain ⟨-, -, -, hz, -⟩ := hf
    change (StatusFlags.ofRFLAGS u3.RFLAGS).ZF = (cmpSpec _ _).ZF at hz
    rw [condHolds_4, hz, cmpSpec_ZF]
    change (wd u2 (I - 168) == (-1 : BitVec 64)) = false
    rw [memory T2]
    exact beq_eq_false_iff_ne.mpr hcap
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (jcc_rel8_effect_step 0x10189c 4 0x24)
    T3 (program_text_slice T3.code 0x189c 2 (by decide +kernel))
    ⟨e3.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hz3]; exact code_ne_boundary outside 0x189e (by omega))
    (by fits [outputPrepChanges])
  have rip4 : u4.RIP = 0x10189e := (jccEffect_not_taken hz3 e4).rip
  have sp4 : stackPtr u4 = I - 168 := sp_keep T4.agrees (by simp [outputPrepChanges]) hsp
  have addr4 : ∀ x, (AddrMode.sib 4 none 0 (.d32 0xc8)).addr u4 x = I + 32 := by
    intro x
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    change rd u4 4 + 200 = _
    rw [show rd u4 4 = I - 168 from sp4]
    bv_omega
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10189e 0x48 (by unfold RexWPrefix; decide) 0
      (AddrMode.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x189e 8 (by decide +kernel))
    ⟨rip4, by
      rw [addr4]
      have h := reads T4 200 (by simp)
      have he : I - 168 + BitVec.ofNat 64 200 = I + 32 := by bv_omega
      rw [he] at h; exact h⟩
    (code_ne_boundary outside 0x18a6 (by omega)) (by fits [outputPrepChanges])
  change (movR64M64Effect 0x10189e 0 (AddrMode.sib 4 none 0 (.d32 0xc8)) u4).Holds u4 u5 at e5
  have val5 : rd u5 0 = cap := by
    have h := e5.writes
    simp only [movR64M64Effect, addr4] at h
    exact h.trans ((memory T4 _).trans houtcap)
  have sp5 : stackPtr u5 = I - 168 := sp_keep T5.agrees (by simp [outputPrepChanges]) hsp
  have addr5 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x10)).addr u5 x = I - 152 := by
    intro x
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    change rd u5 4 + 16 = _
    rw [show rd u5 4 = I - 168 from sp5]
    bv_omega
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1018a6 0x48 (by unfold RexWPrefix; decide) 2
      (AddrMode.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x18a6 5 (by decide +kernel))
    ⟨e5.rip, by
      rw [addr5]
      have h := reads T5 16 (by simp)
      have he : I - 168 + BitVec.ofNat 64 16 = I - 152 := by bv_omega
      rw [he] at h; exact h⟩
    (code_ne_boundary outside 0x18ab (by omega)) (by fits [outputPrepChanges])
  change (movR64M64Effect 0x1018a6 2 (AddrMode.sib 4 none 0 (.d8 0x10)) u5).Holds u5 u6 at e6
  have val6 : rd u6 2 = len := by
    have h := e6.writes
    simp only [movR64M64Effect, addr5] at h
    exact h.trans ((memory T5 _).trans hlen)
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step
    (cmp_r64_r64_effect_step 0x1018ab 0x48 0xc2 (by unfold RexWPrefix; decide) (by decide))
    T6 (program_text_slice T6.code 0x18ab 3 (by decide +kernel))
    e6.rip (code_ne_boundary outside 0x18ae (by omega)) (by fits [outputPrepChanges])
  change (cmpR64R64Effect 0x1018ab 2 0 u6).Holds u6 u7 at e7
  have cap6 : rd u6 0 = cap := (e6.agrees.read (by simp)).trans val5
  have hz7 : condHolds 7 (StatusFlags.ofRFLAGS u7.RFLAGS) = false := by
    have hf := e7.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hf
    obtain ⟨hc, -, -, hz, -⟩ := hf
    change (StatusFlags.ofRFLAGS u7.RFLAGS).CF = (cmpSpec _ _).CF at hc
    change (StatusFlags.ofRFLAGS u7.RFLAGS).ZF = (cmpSpec _ _).ZF at hz
    rw [condHolds_7, hc, hz, cmpSpec_ZF]
    change (!(decide ((rd u6 2).toNat < (rd u6 0).toNat) || (rd u6 2 == rd u6 0))) = false
    rw [val6, cap6]
    by_cases heq : len = cap
    · simp [heq]
    · have hne : len.toNat ≠ cap.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
      have hlt : len.toNat < cap.toNat := by omega
      simp [hlt]
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step
    (jcc_rel8_effect_step 0x1018ae 7 0x5a)
    T7 (program_text_slice T7.code 0x18ae 2 (by decide +kernel))
    ⟨e7.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hz7]; exact code_ne_boundary outside 0x18b0 (by omega))
    (by fits [outputPrepChanges])
  have rip8 : u8.RIP = 0x1018b0 := (jccEffect_not_taken hz7 e8).rip
  have sp8 : stackPtr u8 = I - 168 := sp_keep T8.agrees (by simp [outputPrepChanges]) hsp
  have addr8 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x8)).addr u8 x = I - 160 := by
    intro x
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    change rd u8 4 + 8 = _
    rw [show rd u8 4 = I - 168 from sp8]
    bv_omega
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1018b0 0x48 (by unfold RexWPrefix; decide) 6
      (AddrMode.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    T8 (program_text_slice T8.code 0x18b0 5 (by decide +kernel))
    ⟨rip8, by
      rw [addr8]
      have h := reads T8 8 (by simp)
      have he : I - 168 + BitVec.ofNat 64 8 = I - 160 := by bv_omega
      rw [he] at h; exact h⟩
    (code_ne_boundary outside 0x18b5 (by omega)) (by fits [outputPrepChanges])
  change (movR64M64Effect 0x1018b0 6 (AddrMode.sib 4 none 0 (.d8 0x8)) u8).Holds u8 u9 at e9
  have val9 : rd u9 6 = heap := by
    have h := e9.writes
    simp only [movR64M64Effect, addr8] at h
    exact h.trans ((memory T8 _).trans hheap)
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1018b5 0x48 0xdf (by unfold RexWPrefix; decide) (by decide))
    T9 (program_text_slice T9.code 0x18b5 3 (by decide +kernel))
    e9.rip (code_ne_boundary outside 0x18b8 (by omega)) (by fits [outputPrepChanges])
  change (movR64R64Effect 0x1018b5 7 3 u9).Holds u9 u10 at e10
  refine ⟨u10, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans (a9.trans a10)))))))), T10, e10.rip,
    sp_keep T10.agrees (by simp [outputPrepChanges]) hsp, ?_, ?_, ?_⟩
  · exact e10.writes.trans ((T9.agrees.read (by simp [outputPrepChanges])).trans hout)
  · exact (e10.agrees.read (by simp)).trans val9
  · exact ((e7.agrees.trans (e8.agrees.trans (e9.agrees.trans e10.agrees))).read (by simp [jccEffect])).trans val6


theorem output_call [Bindings] {v b : RamState} {boundary : ReturnBoundary}
    {cs : List Component}
    (outside : ¬ InProgram boundary.rip) (T0 : GTrack cs b v)
    (pre : CallMemPre 0x1018b8 (.rip 0xffaea) v)
    (target : wd v 0x2013a8 = 0x102dc0)
    (fitsCall : Fits cs (callEffect (callMemPtr 0x1018b8 (.rip 0xffaea)) 0x1018be v).components) :
    ∃ w, Advances boundary 1 v w ∧ GTrack cs b w ∧
      w.RIP = 0x102dc0 ∧ stackPtr w = stackPtr v - 8 ∧
      wd w (stackPtr v - 8) = 0x1018be ∧
      (callEffect (callMemPtr 0x1018b8 (.rip 0xffaea)) 0x1018be v).Holds v w := by
  have ht : callMemPtr 0x1018b8 (.rip 0xffaea) v = 0x102dc0 := target
  obtain ⟨w, a, T, e⟩ := gtrack_step
    (call_m64_effect_step 0x1018b8 (.rip 0xffaea) (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x18b8 6 (by decide +kernel)) pre
    (by change callMemPtr _ _ _ ≠ _; rw [ht]; exact code_ne_boundary outside 0x2dc0 (by omega)) fitsCall
  exact ⟨w, a, T, e.rip.trans ht, e.writes.1, e.writes.2, e⟩

def outputReturnChanges : List Component := [.reg 0, .flags, .rip] ++ outputTailChanges

theorem output_finish [bindings : Bindings] {initial v : RamState}
    (hS : EntryStack initial) (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2 ^ 32)
    (ready : ReadyToStep v) (code : CodeIn Extracted.programImage v)
    (machine : SupportedIntegerMachineState bindings.processor v)
    (env : MachineRamUnitStrideDecodable bindings v) (df : DirectionFlagUnset v)
    (rip : v.RIP = 0x1018be) (rsp : stackPtr v = stackPtr initial - 168)
    (present : RetPresent (stackPtr initial) v)
    (ret : wd v (stackPtr initial) = (returnBoundary initial).rip)
    (save3 : wd v (stackPtr initial - 48) = initial.regValue .rbx)
    (save12 : wd v (stackPtr initial - 40) = initial.regValue .r12)
    (save13 : wd v (stackPtr initial - 32) = initial.regValue .r13)
    (save14 : wd v (stackPtr initial - 24) = initial.regValue .r14)
    (save15 : wd v (stackPtr initial - 16) = initial.regValue .r15)
    (save5 : wd v (stackPtr initial - 8) = initial.regValue .rbp) :
    ∃ fuel fin, Returns (returnBoundary initial) fuel v fin ∧
      SupportedIntegerMachineState bindings.processor fin ∧
      MachineRamUnitStrideDecodable bindings fin ∧
      CalleeSavedRegistersUnchanged initial fin ∧ DirectionFlagUnset fin ∧
      AgreesExcept outputReturnChanges v fin ∧ fin.external = v.external ∧ rd fin 0 = 0 := by
  obtain ⟨u, au, Tu, ripu, zerou⟩ := output_success outside
    (show GTrack [.reg 0, .flags, .rip] v v from ⟨ready, code, AgreesExcept.refl _ _⟩) rip
  have mu : ∀ a, wd u a = wd v a := mem_keep Tu.agrees (by simp [Component.isMem])
  obtain ⟨n, fin, af, rf, ag, r3, r12, r13, r14, r15, r5⟩ := output_tail hS outside low
    (show GTrack outputTailChanges u u from ⟨Tu.ready, Tu.code, AgreesExcept.refl _ _⟩) ripu
    (sp_keep Tu.agrees (by simp) rsp) (present.of_agrees Tu.agrees)
    ((mu _).trans ret)
  have all : AgreesExcept outputReturnChanges v fin := Tu.agrees.trans ag
  refine ⟨_, fin, au.returns af,
    ⟨rf.cpu, SupportedSSE.of_agreesExcept all machine.sse, rf.memory, rf.ready⟩,
    ⟨rf.smrr, rf.memoryType, env.stringStride, rf.features.lzcnt⟩,
    ?_, all.directionFlagClear (by simp [outputReturnChanges, outputTailChanges]) df,
    all, all.external (fun c hc x => nonmem_not_covers ?_ x),
    (ag.read (by simp [outputTailChanges])).trans zerou⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r3.trans ((mu _).trans save3)
    · exact r5.trans ((mu _).trans save5)
    · exact r12.trans ((mu _).trans save12)
    · exact r13.trans ((mu _).trans save13)
    · exact r14.trans ((mu _).trans save14)
    · exact r15.trans ((mu _).trans save15)
  · simp only [outputReturnChanges, outputTailChanges, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

def outputEntryChanges (initial : RamState) : List Component :=
  outputPrepChanges ++ [.reg 4, .mem (stackPtr initial - 176) 8, .rip]

theorem output_enter_memcpy [Bindings] {initial v : RamState}
    {heap len cap out : BitVec 64}
    (hS : EntryStack initial) (outside : ¬ InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep v) (code : CodeIn Extracted.programImage v)
    (grows : Grows initial v)
    (hrip : v.RIP = 0x101893) (hsp : stackPtr v = stackPtr initial - 168)
    (hzero : rd v 0 = 0) (hout : rd v 3 = out)
    (hread : ∀ d ∈ [0, 8, 16, 200],
      MemReadable v (stackPtr initial - 168 + BitVec.ofNat 64 d) 8)
    (hcap : wd v (stackPtr initial - 168) ≠ -1)
    (hlen : wd v (stackPtr initial - 152) = len)
    (hheap : wd v (stackPtr initial - 160) = heap)
    (houtcap : wd v (stackPtr initial + 32) = cap) (hroom : len.toNat ≤ cap.toNat) :
    ∃ w, Advances (returnBoundary initial) 11 v w ∧
      ReadyToStep w ∧ CodeIn Extracted.programImage w ∧
      AgreesExcept (outputEntryChanges initial) v w ∧
      w.RIP = 0x102dc0 ∧ stackPtr w = stackPtr initial - 176 ∧
      (returnBoundary w).rip = 0x1018be ∧ rd w 7 = out ∧ rd w 6 = heap ∧ rd w 2 = len := by
  obtain ⟨u, au, Tu, ripu, rspu, dstu, srcu, lenu⟩ := output_prepare outside
    (show GTrack outputPrepChanges v v from ⟨ready, code, AgreesExcept.refl _ _⟩)
    hrip hsp hzero hout hread hcap hlen hheap houtcap hroom
  have gu := grows.step Tu.agrees
  have push : pushAddr u = stackPtr initial - 176 := by rw [pushAddr, rspu]; bv_omega
  have target : callMemPtr 0x1018b8 (.rip 0xffaea) u = 0x102dc0 :=
    MemoryContracts.memcpy_slot u Tu.code
  have ptrRead : MemReadable u 0x2013a8 8 := by
    have hs := Tu.code.slice_of_section (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
      (by simp [Extracted.programSections]) 0x13a8 8 (by decide +kernel)
    refine ⟨by decide, ?_⟩
    intro i hi
    have hl : i < (Extracted.rodataBytes.toListFrom 0x13a8 8).length := by
      rw [chunked_toListFrom_length]; omega
    have he := hs.bytesAt i hl
    change (u.external[(Extracted.rodataAddress + BitVec.ofNat 64 0x13a8) + BitVec.ofNat 64 i]?).isSome
    rw [he]; rfl
  have pre : CallMemPre 0x1018b8 (.rip 0xffaea) u := by
    refine ⟨⟨⟨ripu, ?_, ?_⟩, ?_⟩, ptrRead⟩
    · rw [push]; exact slot_writable hS gu (k := 176) (by omega) (by omega)
    · rw [push]; exact slot_apart hS (k := 176) (by omega) (by omega) (code_inProgram 0x18b8 6 (by omega))
    · rw [target]; decide
  have fit : Fits [.reg 4, .mem (stackPtr initial - 176) 8, .rip]
      (callEffect (callMemPtr 0x1018b8 (.rip 0xffaea)) 0x1018be u).components := by
    simp only [callEffect, pushEffect_components, push, Fits, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨.inl ⟨rfl, by simp⟩, .inr ⟨rfl, ?_⟩, .inl ⟨rfl, by simp⟩⟩
    intro x hx
    refine ⟨⟨_, by simp, hx⟩, ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    have ha := slot_toNat (I := stackPtr initial) (k := 176) (i := i)
      (by have := hS.room; omega) hS.top (by omega)
    change (stackPtr initial - 176 + BitVec.ofNat 64 i).toNat = _ at ha
    apply hS.outside <;> rw [ha] <;> have := hS.room <;> omega
  obtain ⟨w, aw, Tw, ripw, rspw, retw, ew⟩ := output_call outside
    (show GTrack [.reg 4, .mem (stackPtr initial - 176) 8, .rip] u u from
      ⟨Tu.ready, Tu.code, AgreesExcept.refl _ _⟩) pre target fit
  have spw : stackPtr w = stackPtr initial - 176 := by rw [rspw, rspu]; bv_omega
  refine ⟨w, au.trans aw, Tw.ready, Tw.code, Tu.agrees.trans Tw.agrees, ripw, spw, ?_, ?_, ?_, ?_⟩
  · change wd w (stackPtr w) = _
    rw [rspw]; exact retw
  · exact (Tw.agrees.read (by simp)).trans dstu
  · exact (Tw.agrees.read (by simp)).trans srcu
  · exact (Tw.agrees.read (by simp)).trans lenu

theorem output_copy_return [bindings : Bindings] {initial s : RamState}
    (hS : EntryStack initial) (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2 ^ 32)
    (boundary : (returnBoundary initial).rip.toNat < 0x102dc0 ∨
      0x102def ≤ (returnBoundary initial).rip.toNat)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (machine : SupportedIntegerMachineState bindings.processor s)
    (env : MachineRamUnitStrideDecodable bindings s) (df : DirectionFlagUnset s)
    (pre : MemoryContracts.MemcpyPre s)
    (rsp : stackPtr s = stackPtr initial - 176)
    (callret : (returnBoundary s).rip = 0x1018be)
    (present : RetPresent (stackPtr initial) s)
    (apart : (MemoryContracts.destination s).Disjoint (Stack.region initial 48))
    (ret : wd s (stackPtr initial) = (returnBoundary initial).rip)
    (save3 : wd s (stackPtr initial - 48) = initial.regValue .rbx)
    (save12 : wd s (stackPtr initial - 40) = initial.regValue .r12)
    (save13 : wd s (stackPtr initial - 32) = initial.regValue .r13)
    (save14 : wd s (stackPtr initial - 24) = initial.regValue .r14)
    (save15 : wd s (stackPtr initial - 16) = initial.regValue .r15)
    (save5 : wd s (stackPtr initial - 8) = initial.regValue .rbp) :
    ∃ fuel fin t, Returns (returnBoundary initial) fuel s fin ∧
      SupportedIntegerMachineState bindings.processor fin ∧
      MachineRamUnitStrideDecodable bindings fin ∧
      CalleeSavedRegistersUnchanged initial fin ∧ DirectionFlagUnset fin ∧
      MemoryWriteFrame s fin #v[MemoryContracts.destination s] ∧
      MemoryContracts.MemcpyResult s t ∧ fin.external = t.external ∧ rd fin 0 = 0 := by
  obtain ⟨n, t, aCopy, post⟩ := MemoryContracts.memcpy_advances env.stringStride
    (returnBoundary initial) boundary s ready code pre
    (by rw [callret]; exact code_ne_boundary outside 0x18be (by omega))
  have frame := post.toCallResult.frame pre.dst.readable.low
  have keep (k : Nat) (hk : k ≤ 48) :
      wd t (stackPtr initial - BitVec.ofNat 64 k) =
      wd s (stackPtr initial - BitVec.ofNat 64 k) := by
    apply memLoad_congr
    intro i hi
    change i < 8 at hi
    simp only [memByte]
    congr 1
    apply frame
    intro r hr inside
    have he : r = MemoryContracts.destination s := by simpa using hr
    subst r
    apply apart _ inside
    have ha := slot_toNat (I := stackPtr initial) (k := k) (i := i)
      (by have := hS.room; omega) hS.top (by omega)
    change (stackPtr initial).toNat - 48 ≤ _ ∧
      _ < (stackPtr initial).toNat - 48 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 48))
    rw [ha]
    constructor <;> have := hS.room <;> omega
  have kt : wd t (stackPtr initial) = (returnBoundary initial).rip := by
    simpa only [BitVec.sub_zero] using (keep 0 (by omega)).trans
      (show wd s (stackPtr initial - BitVec.ofNat 64 0) = _ from by simpa using ret)
  have sp : stackPtr t = stackPtr initial - 168 := by rw [post.rsp, rsp]; bv_omega
  obtain ⟨m, fin, af, mf, ef, cf, dfinal, ag, mem, zero⟩ := output_finish hS outside low
    post.ready (post.toCallResult.codeIn pre.dst code)
    ⟨post.ready.cpu, SupportedSSE.of_agreesExcept post.agrees machine.sse,
      post.ready.memory, post.ready.ready⟩
    ⟨post.ready.smrr, post.ready.memoryType, env.stringStride, post.ready.features.lzcnt⟩
    ⟨post.toCallResult.directionFlagClear df.df⟩
    (post.rip.trans callret) sp (present.of_agrees post.agrees) kt
    ((keep 48 (by omega)).trans save3) ((keep 40 (by omega)).trans save12)
    ((keep 32 (by omega)).trans save13) ((keep 24 (by omega)).trans save14)
    ((keep 16 (by omega)).trans save15) ((keep 8 (by omega)).trans save5)
  refine ⟨_, fin, t, aCopy.returns af, mf, ef, cf, dfinal, ?_, post, mem, zero⟩
  intro a ha
  rw [mem]
  exact frame a ha

theorem output_entry_word_kept {initial v w : RamState}
    (hS : EntryStack initial) (ag : AgreesExcept (outputEntryChanges initial) v w)
    {k : Nat} (hk : k ≤ 168) :
    wd w (stackPtr initial - BitVec.ofNat 64 k) =
      wd v (stackPtr initial - BitVec.ofNat 64 k) := by
  apply gload ag
  intro c hc i hi
  simp only [outputEntryChanges, outputPrepChanges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals try exact fun h => h
  rintro ⟨j, hj, he⟩
  have ha := slot_toNat (I := stackPtr initial) (k := k) (i := i)
    (by have := hS.room; omega) hS.top (by omega)
  have hb := slot_toNat (I := stackPtr initial) (k := 176) (i := j)
    (by have := hS.room; omega) hS.top (by omega)
  change (stackPtr initial - 176 + BitVec.ofNat 64 j).toNat = _ at hb
  have heq := congrArg BitVec.toNat he
  rw [ha, hb] at heq
  have := hS.room
  omega

theorem output_entry_frame {initial v w : RamState}
    (hS : EntryStack initial) (ag : AgreesExcept (outputEntryChanges initial) v w) :
    MemoryWriteFrame v w #v[Stack.region initial encrypt.minStackBytes] := by
  apply ag.memoryWriteFrame
  intro c hc a cover
  simp only [outputEntryChanges, outputPrepChanges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals try exact cover.elim
  obtain ⟨i, hi, rfl⟩ := cover
  refine ⟨Stack.region initial encrypt.minStackBytes, by simp, ?_⟩
  have ha := slot_toNat (I := stackPtr initial) (k := 176) (i := i)
    (by have := hS.room; omega) hS.top (by omega)
  change (stackPtr initial - 176 + BitVec.ofNat 64 i).toNat = _ at ha
  change (stackPtr initial).toNat - 1168 ≤ _ ∧
    _ < (stackPtr initial).toNat - 1168 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
  rw [ha]
  constructor <;> have := hS.room <;> omega

end ChaCha20Poly1305.Proofs.Encrypt
