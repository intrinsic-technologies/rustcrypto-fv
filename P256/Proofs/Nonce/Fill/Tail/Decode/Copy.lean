import P256.Proofs.Nonce.Fill.Tail.Decode.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Copy

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Nonce.Fill.Tail.Decode
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

def components (s : RamState) : List Component :=
  [.mem (stackPtr s + 152) 8, .mem (stackPtr s + 160) 8,
    .mem (stackPtr s + 168) 8, .mem (stackPtr s + 176) 8, .reg 0, .reg 1, .rip]

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (stage : Context initial s orderAddress state) (rip : s.RIP = 0x107530) :
    ∃ t, Advances boundary 8 s t ∧ Context initial t orderAddress state ∧ t.RIP = 0x107567 ∧
      AgreesExcept (components s) s t ∧
      ∀ j < 4, memLoad t.external (stackPtr t + 152 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr s + 104 + BitVec.ofNat 64 (8*j)) 64 := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x107530 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7530 _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, Fill.stack_readable pre stage.toFrame
        (offset := 128) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7538 (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers r1 g1 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have sp1 : stackPtr s1 = stackPtr s := by rw [f1.rsp, stage.rsp]
  have v1 : (Operand.reg 0 : Operand 64).read s1 = memLoad s.external (stackPtr s + 128) 64 := by
    have h : (Operand.reg 0 : Operand 64).read s1 = memLoad s.external (stackPtr s + 128) 64 := e1.writes
    exact h
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_r64_effect_step 0x107538 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x7538 _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, Fill.stack_writable8 pre f1.toFrame (offset := 176) (by decide) (by decide),
        Fill.stack_code pre f1.toFrame
          (offset := 176) (len := 8) (codeOffset := 0x7538) (codeLen := 8)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7540 (by decide)))
  have raw2 : AgreesExcept [.mem (stackPtr s1 + 176) 8, .rip] s1 s2 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := context_after_store pre f1 r2 raw2 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have sp2 : stackPtr s2 = stackPtr s := by rw [f2.rsp, stage.rsp]
  have g2 : AgreesExcept [.mem (stackPtr s + 176) 8, .rip] s1 s2 := by
    simpa only [sp1] using raw2
  have w2 : memLoad s2.external (stackPtr s + 176) 64 = memLoad s.external (stackPtr s + 128) 64 := by
    have h : memLoad s2.external (stackPtr s1 + 176) 64 = (Operand.reg 0 : Operand 64).read s1 := e2.writes
    rw [sp1] at h
    exact h.trans v1
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r64_m64_effect_step 0x107540 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7540 _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, Fill.stack_readable pre f2.toFrame (offset := 120) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7545 (by decide)))
  have g3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers r3 g3 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
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
    (mov_m64_r64_effect_step 0x107545 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7545 _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, Fill.stack_writable8 pre f3.toFrame (offset := 168) (by decide) (by decide),
        Fill.stack_code pre f3.toFrame
          (offset := 168) (len := 8) (codeOffset := 0x7545) (codeLen := 8)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x754d (by decide)))
  have raw4 : AgreesExcept [.mem (stackPtr s3 + 168) 8, .rip] s3 s4 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := context_after_store pre f3 r4 raw4 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have sp4 : stackPtr s4 = stackPtr s := by rw [f4.rsp, stage.rsp]
  have g4 : AgreesExcept [.mem (stackPtr s + 168) 8, .rip] s3 s4 := by
    simpa only [sp3] using raw4
  have w4 : memLoad s4.external (stackPtr s + 168) 64 = memLoad s.external (stackPtr s + 120) 64 := by
    have h : memLoad s4.external (stackPtr s3 + 168) 64 = (Operand.reg 0 : Operand 64).read s3 := e4.writes
    rw [sp3] at h
    exact h.trans v3
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_r64_m64_effect_step 0x10754d 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl).advances
      (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x754d _
        (by decide +kernel) (by decide +kernel))
      ⟨e4.rip, Fill.stack_readable pre f4.toFrame (offset := 104) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7552 (by decide)))
  have g5 : AgreesExcept [.reg 0, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers r5 g5 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
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
    (mov_r64_m64_effect_step 0x107552 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl).advances
      (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7552 _
        (by decide +kernel) (by decide +kernel))
      ⟨e5.rip, Fill.stack_readable pre f5.toFrame (offset := 112) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7557 (by decide)))
  have g6 : AgreesExcept [.reg 1, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers r6 g6 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
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
    (mov_m64_r64_effect_step 0x107557 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl).advances
      (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7557 _
        (by decide +kernel) (by decide +kernel))
      ⟨e6.rip, Fill.stack_writable8 pre f6.toFrame (offset := 160) (by decide) (by decide),
        Fill.stack_code pre f6.toFrame
          (offset := 160) (len := 8) (codeOffset := 0x7557) (codeLen := 8)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x755f (by decide)))
  have raw7 : AgreesExcept [.mem (stackPtr s6 + 160) 8, .rip] s6 s7 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := context_after_store pre f6 r7 raw7 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have sp7 : stackPtr s7 = stackPtr s := by rw [f7.rsp, stage.rsp]
  have g7 : AgreesExcept [.mem (stackPtr s + 160) 8, .rip] s6 s7 := by
    simpa only [sp6] using raw7
  have w7 : memLoad s7.external (stackPtr s + 160) 64 = memLoad s.external (stackPtr s + 112) 64 := by
    have h : memLoad s7.external (stackPtr s6 + 160) 64 = (Operand.reg 1 : Operand 64).read s6 := e7.writes
    rw [sp6] at h
    exact h.trans v6
  obtain ⟨s8, a8, r8, e8⟩ :=
    (mov_m64_r64_effect_step 0x10755f 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl).advances
      (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x755f _
        (by decide +kernel) (by decide +kernel))
      ⟨e7.rip, Fill.stack_writable8 pre f7.toFrame (offset := 152) (by decide) (by decide),
        Fill.stack_code pre f7.toFrame
          (offset := 152) (len := 8) (codeOffset := 0x755f) (codeLen := 8)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7567 (by decide)))
  have raw8 : AgreesExcept [.mem (stackPtr s7 + 152) 8, .rip] s7 s8 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e8.agrees
  have f8 := context_after_store pre f7 r8 raw8 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have sp8 : stackPtr s8 = stackPtr s := by rw [f8.rsp, stage.rsp]
  have g8 : AgreesExcept [.mem (stackPtr s + 152) 8, .rip] s7 s8 := by
    simpa only [sp7] using raw8
  have w8 : memLoad s8.external (stackPtr s + 152) 64 = memLoad s.external (stackPtr s + 104) 64 := by
    have h : memLoad s8.external (stackPtr s7 + 152) 64 = (Operand.reg 0 : Operand 64).read s7 := e8.writes
    rw [sp7] at h
    exact h.trans (((g6.trans g7).read (n := 64) (r := 0) (by simp)).trans v5)
  refine ⟨s8, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8, f8, e8.rip, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono (by simp [components]), ?_⟩
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  · change memLoad s8.external (stackPtr s8 + 152) 64 = memLoad s.external (stackPtr s + 104) 64
    rw [sp8]
    exact w8
  · change memLoad s8.external (stackPtr s8 + 160) 64 = memLoad s.external (stackPtr s + 112) 64
    rw [sp8]
    refine (read_mem_of_agrees g8 _ ?_).trans w7
    intro i hi c hc
    simp only [ List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · change memLoad s8.external (stackPtr s8 + 168) 64 = memLoad s.external (stackPtr s + 120) 64
    rw [sp8]
    refine (read_mem_of_agrees (((g5.trans g6).trans g7).trans g8) _ ?_).trans w4
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · change memLoad s8.external (stackPtr s8 + 176) 64 = memLoad s.external (stackPtr s + 128) 64
    rw [sp8]
    refine (read_mem_of_agrees (((((g3.trans g4).trans g5).trans g6).trans g7).trans g8) _ ?_).trans w2
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl))
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel

end P256.Proofs.Nonce.Fill.Tail.Decode.Copy
