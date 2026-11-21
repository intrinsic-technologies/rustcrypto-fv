import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
open ChaCha20Poly1305.Proofs.Wrapper

def appendCs (I : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .flags, .rip,
    .mem (I - 112) 8, .mem (I - 120) 8, .mem (I - 176) 8]

theorem stack_readable {initial u : RamState} (hS : EntryStack initial)
    (hg : Grows initial u) {k n : Nat} (hk : k ≤ 1104) (hn : n ≤ k + 8) :
    MemReadable u (stackPtr initial - BitVec.ofNat 64 k) n := by
  have hr := hS.room
  have ht := hS.top
  refine ⟨by rw [slot_toNat0 (by omega)]; omega, ?_⟩
  intro i hi
  apply hg
  apply hS.allocated <;> rw [slot_toNat (by omega) ht (by omega)] <;> omega

theorem append_slot_fits {initial : RamState} (hS : EntryStack initial) {k : Nat}
    (hk : k = 112 ∨ k = 120 ∨ k = 176) :
    ∀ x, (Component.mem (stackPtr initial - BitVec.ofNat 64 k) 8).Covers x →
      (∃ d ∈ appendCs (stackPtr initial), d.Covers x) ∧ ¬ InProgram x := by
  intro x hx
  refine ⟨⟨_, ?_, hx⟩, ?_⟩
  · rcases hk with rfl | rfl | rfl <;> simp [appendCs]
  · obtain ⟨i, hi, rfl⟩ := hx
    have hr := hS.room
    have ht := hS.top
    apply hS.outside <;> rw [slot_toNat (by omega) ht (by omega)] <;> omega

theorem to_append [Machine.Bindings] {initial t : RamState}
    (hS : EntryStack initial) (hg : Grows initial t)
    {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (T0 : GTrack (appendCs (stackPtr initial)) t t)
    (hrip : t.RIP = 0x101866) (hsp : stackPtr t = stackPtr initial - 168)
    (hres : (t.external[stackPtr initial - 137]?).getD 0 = 0) :
    ∃ n u, Advances boundary n t u ∧ GTrack (appendCs (stackPtr initial)) t u ∧
      u.RIP = 0x101fb0 ∧ stackPtr u = stackPtr initial - 176 ∧
      rd u 7 = stackPtr initial - 168 ∧ rd u 6 = stackPtr initial - 120 ∧
      rd u 2 = 16 ∧ wd u (stackPtr initial - 176) = 0x101893 ∧
      wd u (stackPtr initial - 120) = wd t (stackPtr initial - 136) ∧
      wd u (stackPtr initial - 112) = wd t (stackPtr initial - 128) := by
  change stackPtr t = stackPtr initial - BitVec.ofNat 64 168 at hsp
  have hA1 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x1f)).addr t x =
      stackPtr initial - BitVec.ofNat 64 137 := rsp_addr hsp 0x1f 31 rfl (by omega)
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (cmp_m8_imm8_effect_step 0x101866 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide)
      (by decide) 1)
    T0 (program_text_slice T0.code 0x1866 5 (by decide +kernel))
    ⟨hrip, by rw [hA1]; exact stack_readable hS hg (k := 137) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x186b (by omega)) (by fits [appendCs])
  change (cmpM8Imm8Effect 0x101866 5 (.sib 4 none 0 (.d8 0x1f)) 1 t).Holds t u1 at e1
  have hsp1 := sp_keep e1.agrees (by simp) hsp
  have hz1 : condHolds 4 (StatusFlags.ofRFLAGS u1.RFLAGS) = false := by
    have hf := e1.flags
    simp only [Effect.FlagsHold, cmpM8Imm8Effect, hA1] at hf
    obtain ⟨-, -, -, hZF, -⟩ := hf
    change (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = (cmpSpec _ _).ZF at hZF
    rw [condHolds_4, hZF, cmpSpec_ZF]
    change (memLoad t.external (stackPtr initial - 137) 8 == 1) = false
    rw [memLoad_8]
    simp only [memByte]
    change (((t.external[stackPtr initial - 137]?).getD 0).toBitVec == 1) = false
    rw [hres]
    decide
  have htgt2 : branchTarget 0x10186b 2 ((0x55 : BitVec 8).signExtend 64) = 0x1018c2 := by decide
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step (jcc_rel8_effect_step 0x10186b 4 0x55)
    T1 (program_text_slice T1.code 0x186b 2 (by decide +kernel))
    ⟨e1.rip, fun _ => by rw [htgt2]; decide⟩
    (by simp only [jccEffect, branchEffect, hz1]
        exact code_ne_boundary hOut 0x186d (by omega))
    (by fits [appendCs])
  have hrip2 : u2.RIP = 0x10186d := (jccEffect_not_taken hz1 e2).rip
  have hsp2 := sp_keep e2.agrees (by simp [jccEffect]) hsp1
  have hA3 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x20)).addr u2 x =
      stackPtr initial - BitVec.ofNat 64 136 := rsp_addr hsp2 0x20 32 rfl (by omega)
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10186d 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x186d 5 (by decide +kernel))
    ⟨hrip2, by rw [hA3]; exact stack_readable hS (hg.step T2.agrees) (k := 136) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x1872 (by omega)) (by fits [appendCs])
  change (movR64M64Effect 0x10186d 0 (.sib 4 none 0 (.d8 0x20)) u2).Holds u2 u3 at e3
  have hsp3 := sp_keep e3.agrees (by simp) hsp2
  have v3 : rd u3 0 = wd u2 (stackPtr initial - BitVec.ofNat 64 136) := by
    have := e3.writes
    simp only [movR64M64Effect, hA3] at this
    exact this
  have hA4 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x28)).addr u3 x =
      stackPtr initial - BitVec.ofNat 64 128 := rsp_addr hsp3 0x28 40 rfl (by omega)
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x101872 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1872 5 (by decide +kernel))
    ⟨e3.rip, by rw [hA4]; exact stack_readable hS (hg.step T3.agrees) (k := 128) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x1877 (by omega)) (by fits [appendCs])
  change (movR64M64Effect 0x101872 1 (.sib 4 none 0 (.d8 0x28)) u3).Holds u3 u4 at e4
  have hsp4 := sp_keep e4.agrees (by simp) hsp3
  have v4 : rd u4 1 = wd u3 (stackPtr initial - BitVec.ofNat 64 128) := by
    have := e4.writes
    simp only [movR64M64Effect, hA4] at this
    exact this
  have hA5 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x38)).addr u4 x =
      stackPtr initial - BitVec.ofNat 64 112 := rsp_addr hsp4 0x38 56 rfl (by omega)
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101877 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x1877 5 (by decide +kernel))
    ⟨e4.rip,
      by simp only [storeAddrAt, hA5]
         exact slot_writable hS (hg.step T4.agrees) (k := 112) (by omega) (by omega),
      by simp only [storeAddrAt, hA5]
         exact slot_apart hS (k := 112) (by omega) (by omega) (code_inProgram 0x1877 5 (by omega))⟩
    (code_ne_boundary hOut 0x187c (by omega))
    (by
      fits [appendCs, hA5]
      exact .inr ⟨rfl, append_slot_fits hS (by omega)⟩)
  change (movM64R64Effect 0x101877 1 (.sib 4 none 0 (.d8 0x38)) u4).Holds u4 u5 at e5
  have hsp5 := sp_keep e5.agrees (by simp) hsp4
  have w5 : wd u5 (stackPtr initial - BitVec.ofNat 64 112) = rd u4 1 := by
    rw [← hA5 (0x101877 + BitVec.ofNat 64 5)]
    exact e5.writes
  have hA6 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x30)).addr u5 x =
      stackPtr initial - BitVec.ofNat 64 120 := rsp_addr hsp5 0x30 48 rfl (by omega)
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x10187c 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x187c 5 (by decide +kernel))
    ⟨e5.rip,
      by simp only [storeAddrAt, hA6]
         exact slot_writable hS (hg.step T5.agrees) (k := 120) (by omega) (by omega),
      by simp only [storeAddrAt, hA6]
         exact slot_apart hS (k := 120) (by omega) (by omega) (code_inProgram 0x187c 5 (by omega))⟩
    (code_ne_boundary hOut 0x1881 (by omega))
    (by
      fits [appendCs, hA6]
      exact .inr ⟨rfl, append_slot_fits hS (by omega)⟩)
  change (movM64R64Effect 0x10187c 0 (.sib 4 none 0 (.d8 0x30)) u5).Holds u5 u6 at e6
  have hsp6 := sp_keep e6.agrees (by simp) hsp5
  have w6 : wd u6 (stackPtr initial - BitVec.ofNat 64 120) = rd u5 0 := by
    rw [← hA6 (0x10187c + BitVec.ofNat 64 5)]
    exact e6.writes
  have k6 : wd u6 (stackPtr initial - BitVec.ofNat 64 112) =
      wd u5 (stackPtr initial - BitVec.ofNat 64 112) := by
    apply gload e6.agrees
    intro c hc i hi
    simp only [movM64R64Effect_components, storeAddrAt, hA6, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · exact slot_not_covers hi (by omega) (by omega) (by omega)
    · exact fun h => h
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x101881 0x48 0xe7 (by unfold RexWPrefix; decide) (by decide))
    T6 (program_text_slice T6.code 0x1881 3 (by decide +kernel))
    e6.rip (code_ne_boundary hOut 0x1884 (by omega)) (by fits [appendCs])
  change (movR64R64Effect 0x101881 7 4 u6).Holds u6 u7 at e7
  have hsp7 := sp_keep e7.agrees (by simp) hsp6
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step
    (lea_r64_effect_step 0x101884 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    T7 (program_text_slice T7.code 0x1884 5 (by decide +kernel))
    e7.rip (code_ne_boundary hOut 0x1889 (by omega))
    (by simp only [Fits, leaR64Effect_components]; simp [appendCs, Component.isMem]; decide)
  change (leaR64Effect 0x101884 6 (.sib 4 none 0 (.d8 0x30)) u7).Holds u7 u8 at e8
  have hsp8 := sp_keep e8.agrees (by simp) hsp7
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step
    (mov_r32_imm32_effect_step 0x101889 0xba (by decide) 16)
    T8 (program_text_slice T8.code 0x1889 5 (by decide +kernel))
    e8.rip (code_ne_boundary hOut 0x188e (by omega)) (by fits [appendCs])
  change (movR32Imm32Effect 0x101889 5 2 16 u8).Holds u8 u9 at e9
  have hsp9 := sp_keep e9.agrees (by simp) hsp8
  have hpa : pushAddr u9 = stackPtr initial - BitVec.ofNat 64 176 := by
    rw [pushAddr, hsp9]; bv_omega
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step
    (call_rel32_effect_step 0x10188e 0x71d (by decide))
    T9 (program_text_slice T9.code 0x188e 5 (by decide +kernel))
    (storePre_slot hS (hg.step T9.agrees) e9.rip hpa (by omega) (by omega)
      (code_inProgram 0x188e 5 (by omega)))
    (code_ne_boundary hOut 0x1fb0 (by omega))
    (by
      simp only [Fits, callEffect, pushEffect_components, hpa]
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨.inl ⟨rfl, by simp [appendCs]⟩, .inr ⟨rfl, append_slot_fits hS (by omega)⟩,
        .inl ⟨rfl, by simp [appendCs]⟩⟩)
  change (callEffect (fun _ => branchTarget 0x10188e 5 ((0x71d : BitVec 32).signExtend 64))
      (0x10188e + BitVec.ofNat 64 5) u9).Holds u9 u10 at e10
  have m10 : ∀ k, k = 112 ∨ k = 120 →
      wd u10 (stackPtr initial - BitVec.ofNat 64 k) = wd u9 (stackPtr initial - BitVec.ofNat 64 k) := by
    intro k hk
    apply gload e10.agrees
    intro c hc i hi
    simp only [callEffect, pushEffect_components, hpa, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact fun h => h
    · exact slot_not_covers hi (by omega) (by omega) (by omega)
    · exact fun h => h
  have m79 : ∀ a, wd u9 a = wd u6 a :=
    mem_keep ((e7.agrees.trans e8.agrees).trans e9.agrees) (by simp [Component.isMem])
  refine ⟨_, u10, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans
    (a7.trans (a8.trans (a9.trans a10)))))))), T10, e10.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (show stackPtr u10 = pushAddr u9 from e10.writes.1).trans hpa
  · show (Operand.reg 7 : Operand 64).read u10 = _
    rw [((e8.agrees.trans e9.agrees).trans e10.agrees).read (by simp), e7.writes,
      ← stackPtr_eq_read, hsp6]
    rfl
  · show (Operand.reg 6 : Operand 64).read u10 = _
    rw [(e9.agrees.trans e10.agrees).read (by simp), e8.writes]
    exact rsp_addr hsp7 0x30 48 rfl (by omega) 0x101889
  · exact (e10.agrees.read (by simp)).trans e9.writes
  · change wd u10 (stackPtr initial - BitVec.ofNat 64 176) = _
    rw [← hpa]; exact e10.writes.2
  · change wd u10 (stackPtr initial - BitVec.ofNat 64 120) = _
    rw [m10 120 (by omega), m79, w6]
    exact ((e4.agrees.trans e5.agrees).read (r := 0) (by simp)).trans
      (v3.trans (mem_keep (e1.agrees.trans e2.agrees)
        (by simp [Component.isMem, jccEffect]) _))
  · change wd u10 (stackPtr initial - BitVec.ofNat 64 112) = _
    rw [m10 112 (by omega), m79, k6, w5, v4]
    exact mem_keep ((e1.agrees.trans e2.agrees).trans e3.agrees)
      (by simp [Component.isMem, jccEffect]) _

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
