import P256.Proofs.Nonce.Initialize.Read.Correct

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Read.Copy

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Nonce.Initialize.Prepare
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

def components (s : RamState) : List Component :=
  [.mem (stackPtr s + 72) 8, .mem (stackPtr s + 80) 8,
    .mem (stackPtr s + 88) 8, .mem (stackPtr s + 96) 8, .reg 0, .reg 1, .rip]

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107962) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x10798d ∧
      AgreesExcept (components s) s t ∧
      ∀ j < 4, memLoad t.external (stackPtr t + 72 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr s + 104 + BitVec.ofNat 64 (8*j)) 64 := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x107962 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7962 _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState
        (offset := 128) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x796a (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have sp1 : stackPtr s1 = stackPtr s := by rw [f1.rsp, stage.rsp]
  have v1 : (Operand.reg 0 : Operand 64).read s1 = memLoad s.external (stackPtr s + 128) 64 := by
    have h : (Operand.reg 0 : Operand 64).read s1 = memLoad s.external (stackPtr s + 128) 64 := e1.writes
    exact h
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_r64_effect_step 0x10796a 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x796a _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, stack_writable8 pre f1 (offset := 96) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f1.toFrameState
          (offset := 96) (len := 8) (codeOffset := 0x796a) (codeLen := 5)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x796f (by decide)))
  have raw2 : AgreesExcept [.mem (stackPtr s1 + 96) 8, .rip] s1 s2 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := after_store pre f1 a2 r2 raw2 (by decide)
  have sp2 : stackPtr s2 = stackPtr s := by rw [f2.rsp, stage.rsp]
  have g2 : AgreesExcept [.mem (stackPtr s + 96) 8, .rip] s1 s2 := by
    simpa only [sp1] using raw2
  have w2 : memLoad s2.external (stackPtr s + 96) 64 = memLoad s.external (stackPtr s + 128) 64 := by
    have h : memLoad s2.external (stackPtr s1 + 96) 64 = (Operand.reg 0 : Operand 64).read s1 := e2.writes
    rw [sp1] at h
    exact h.trans v1
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r64_m64_effect_step 0x10796f 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x796f _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, ScalarFrame.stack_readable pre.toCalleePre f2.toFrameState
        (offset := 120) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7974 (by decide)))
  have g3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  have sp3 : stackPtr s3 = stackPtr s := by rw [f3.rsp, stage.rsp]
  have v3 : (Operand.reg 0 : Operand 64).read s3 = memLoad s.external (stackPtr s + 120) 64 := by
    have h : (Operand.reg 0 : Operand 64).read s3 = memLoad s2.external (stackPtr s2 + 120) 64 := e3.writes
    rw [sp2] at h
    refine h.trans (read_mem_of_agrees (g1.trans g2) _ ?_)
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_m64_r64_effect_step 0x107974 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7974 _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, stack_writable8 pre f3 (offset := 88) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f3.toFrameState
          (offset := 88) (len := 8) (codeOffset := 0x7974) (codeLen := 5)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7979 (by decide)))
  have raw4 : AgreesExcept [.mem (stackPtr s3 + 88) 8, .rip] s3 s4 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := after_store pre f3 a4 r4 raw4 (by decide)
  have sp4 : stackPtr s4 = stackPtr s := by rw [f4.rsp, stage.rsp]
  have g4 : AgreesExcept [.mem (stackPtr s + 88) 8, .rip] s3 s4 := by
    simpa only [sp3] using raw4
  have w4 : memLoad s4.external (stackPtr s + 88) 64 = memLoad s.external (stackPtr s + 120) 64 := by
    have h : memLoad s4.external (stackPtr s3 + 88) 64 = (Operand.reg 0 : Operand 64).read s3 := e4.writes
    rw [sp3] at h
    exact h.trans v3
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_r64_m64_effect_step 0x107979 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl).advances
      (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x7979 _
        (by decide +kernel) (by decide +kernel))
      ⟨e4.rip, ScalarFrame.stack_readable pre.toCalleePre f4.toFrameState
        (offset := 104) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x797e (by decide)))
  have g5 : AgreesExcept [.reg 0, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  have sp5 : stackPtr s5 = stackPtr s := by rw [f5.rsp, stage.rsp]
  have v5 : (Operand.reg 0 : Operand 64).read s5 = memLoad s.external (stackPtr s + 104) 64 := by
    have h : (Operand.reg 0 : Operand 64).read s5 = memLoad s4.external (stackPtr s4 + 104) 64 := e5.writes
    rw [sp4] at h
    refine h.trans (read_mem_of_agrees (((g1.trans g2).trans g3).trans g4) _ ?_)
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  obtain ⟨s6, a6, r6, e6⟩ :=
    (mov_r64_m64_effect_step 0x10797e 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl).advances
      (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x797e _
        (by decide +kernel) (by decide +kernel))
      ⟨e5.rip, ScalarFrame.stack_readable pre.toCalleePre f5.toFrameState
        (offset := 112) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7983 (by decide)))
  have g6 : AgreesExcept [.reg 1, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have sp6 : stackPtr s6 = stackPtr s := by rw [f6.rsp, stage.rsp]
  have v6 : (Operand.reg 1 : Operand 64).read s6 = memLoad s.external (stackPtr s + 112) 64 := by
    have h : (Operand.reg 1 : Operand 64).read s6 = memLoad s5.external (stackPtr s5 + 112) 64 := e6.writes
    rw [sp5] at h
    refine h.trans (read_mem_of_agrees ((((g1.trans g2).trans g3).trans g4).trans g5) _ ?_)
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  obtain ⟨s7, a7, r7, e7⟩ :=
    (mov_m64_r64_effect_step 0x107983 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl).advances
      (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7983 _
        (by decide +kernel) (by decide +kernel))
      ⟨e6.rip, stack_writable8 pre f6 (offset := 80) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f6.toFrameState
          (offset := 80) (len := 8) (codeOffset := 0x7983) (codeLen := 5)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7988 (by decide)))
  have raw7 : AgreesExcept [.mem (stackPtr s6 + 80) 8, .rip] s6 s7 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := after_store pre f6 a7 r7 raw7 (by decide)
  have sp7 : stackPtr s7 = stackPtr s := by rw [f7.rsp, stage.rsp]
  have g7 : AgreesExcept [.mem (stackPtr s + 80) 8, .rip] s6 s7 := by
    simpa only [sp6] using raw7
  have w7 : memLoad s7.external (stackPtr s + 80) 64 = memLoad s.external (stackPtr s + 112) 64 := by
    have h : memLoad s7.external (stackPtr s6 + 80) 64 = (Operand.reg 1 : Operand 64).read s6 := e7.writes
    rw [sp6] at h
    exact h.trans v6
  obtain ⟨s8, a8, r8, e8⟩ :=
    (mov_m64_r64_effect_step 0x107988 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl).advances
      (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x7988 _
        (by decide +kernel) (by decide +kernel))
      ⟨e7.rip, stack_writable8 pre f7 (offset := 72) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f7.toFrameState
          (offset := 72) (len := 8) (codeOffset := 0x7988) (codeLen := 5)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x798d (by decide)))
  have raw8 : AgreesExcept [.mem (stackPtr s7 + 72) 8, .rip] s7 s8 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e8.agrees
  have f8 := after_store pre f7 a8 r8 raw8 (by decide)
  have sp8 : stackPtr s8 = stackPtr s := by rw [f8.rsp, stage.rsp]
  have g8 : AgreesExcept [.mem (stackPtr s + 72) 8, .rip] s7 s8 := by
    simpa only [sp7] using raw8
  have w8 : memLoad s8.external (stackPtr s + 72) 64 = memLoad s.external (stackPtr s + 104) 64 := by
    have h : memLoad s8.external (stackPtr s7 + 72) 64 = (Operand.reg 0 : Operand 64).read s7 := e8.writes
    rw [sp7] at h
    exact h.trans (((g6.trans g7).read (n := 64) (r := 0) (by simp)).trans v5)
  refine ⟨s8, f8, e8.rip, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono (by simp [components]), ?_⟩
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  · change memLoad s8.external (stackPtr s8 + 72) 64 = memLoad s.external (stackPtr s + 104) 64
    rw [sp8]
    exact w8
  · change memLoad s8.external (stackPtr s8 + 80) 64 = memLoad s.external (stackPtr s + 112) 64
    rw [sp8]
    refine (read_mem_of_agrees g8 _ ?_).trans w7
    intro i hi c hc
    simp only [ List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · change memLoad s8.external (stackPtr s8 + 88) 64 = memLoad s.external (stackPtr s + 120) 64
    rw [sp8]
    refine (read_mem_of_agrees (((g5.trans g6).trans g7).trans g8) _ ?_).trans w4
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · change memLoad s8.external (stackPtr s8 + 96) 64 = memLoad s.external (stackPtr s + 128) 64
    rw [sp8]
    refine (read_mem_of_agrees (((((g3.trans g4).trans g5).trans g6).trans g7).trans g8) _ ?_).trans w2
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel

end P256.Proofs.Nonce.Initialize.Read.Copy
