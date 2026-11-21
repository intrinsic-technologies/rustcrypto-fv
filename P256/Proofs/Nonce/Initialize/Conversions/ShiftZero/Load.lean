import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Memory
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftRight.Byte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftRight

structure LoadedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x109565
  outputSaved : memLoad t.external (stackPtr s - 56#64) 64 = s.regValue .rdi
  rdx : t.regValue .rdx = 0
  r13 : t.regValue .r13 = a.l3
  r15 : t.regValue .r15 = a.l2
  r10 : t.regValue .r10 = a.l0
  r14 : t.regValue .r14 = a.l1
  rax : t.regValue .rax = 0

set_option maxHeartbeats 1000000 in
theorem load_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : PreparedState s t boundary a) :
    ∃ u, LoadedState s u boundary a := by
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (mov_m64_r64_effect_step 0x10954a 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances state.ready
      (programText_slice (programLoaded_codeIn state.loaded) 0x954a _ (by decide) (by decide +kernel))
      ⟨state.rip, state.toStage.scratch_word_writable pre (by decide) (by decide),
        state.toStage.scratch_code_apart pre (offset := 16) (len := 8)
          (codeOffset := 0x954a) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x954f (by decide)))
  have ce1 : (movM64R64Effect 0x10954a 7 (.sib 4 none 0 (.d8 16)) t).components =
      [.mem (rspOf t + 16#64) 8, .rip] := by
    simp [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f1 : AgreesExcept [.mem (rspOf t + 16#64) 8, .rip] t t1 := by
    have h := e1.agrees
    change AgreesExcept (movM64R64Effect 0x10954a 7 (.sib 4 none 0 (.d8 16)) t).components t t1 at h
    rw [ce1] at h
    exact h
  have st1 := state.toStage.of_effect pre run1 ready1 e1
    (by change ∀ c ∈ (movM64R64Effect 0x10954a 7 (.sib 4 none 0 (.d8 16)) t).components, BodyComponent (rspOf t) c
        rw [ce1]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨16, rfl, by decide⟩
        · trivial)
    (by simp)
  have ptr1 : t1.regValue .rsi = s.regValue .rsi :=
    (f1.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have saved1 : memLoad t1.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    have h : memLoad t1.external (rspOf t + 16#64) 64 = t.regValue .rdi := e1.writes
    rw [state.toStage.scratch_address (offset := 16) (by decide), state.rdi] at h
    exact h
  have input1 : readLimbs t1 (s.regValue .rsi) = a := by
    have reads (off : Nat) (bound : off + 8 ≤ 32) :=
      body_input_read pre state.toStage f1
        (by
          intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact ⟨16, rfl, by decide⟩
          · trivial) bound
    rw [← state.input]
    unfold readLimbs
    congr 1
    · simpa only [Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using reads 0 (by decide)
    · exact reads 8 (by decide)
    · exact reads 16 (by decide)
    · exact reads 24 (by decide)
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x10954f 0x4c (by simp [RexWPrefix]) 5
      (.base 6 (.d8 24)) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn st1.loaded) 0x954f _ (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change MemReadable t1 (t1.regValue .rsi + 24#64) 8
        rw [ptr1]
        exact st1.input_readable pre (offset := 24) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9553 (by decide)))
  have f2 : AgreesExcept [.reg 13, .rip] t1 t2 := e2.agrees
  have st2 := st1.of_effect pre run2 ready2 e2
    (by change ∀ c ∈ [.reg 13, .rip], BodyComponent (rspOf t1) c
        simp [BodyComponent]) (by simp; decide)
  have ptr2 : t2.regValue .rsi = s.regValue .rsi :=
    (f2.read (r := 6) (n := 64) (by simp)).trans ptr1
  have mem2 : t2.external = t1.external :=
    (f2.external (by simp [Component.Covers]))
  have v2 : (Operand.reg 13 : Operand 64).read t2 = a.l3 := by
    have h : (Operand.reg 13 : Operand 64).read t2 =
      memLoad t1.external (t1.regValue .rsi + 24#64) 64 := e2.writes
    rw [ptr1] at h
    rw [h]
    have ha := congrArg Limbs.l3 input1
    simpa [readLimbs, Operand.read] using ha
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (mov_r64_m64_effect_step 0x109553 0x4c (by simp [RexWPrefix]) 7
      (.base 6 (.d8 16)) (by decide) rfl rfl).advances ready2
      (programText_slice (programLoaded_codeIn st2.loaded) 0x9553 _ (by decide) (by decide +kernel))
      ⟨e2.rip, by
        change MemReadable t2 (t2.regValue .rsi + 16#64) 8
        rw [ptr2]
        exact st2.input_readable pre (offset := 16) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9557 (by decide)))
  have f3 : AgreesExcept [.reg 15, .rip] t2 t3 := e3.agrees
  have st3 := st2.of_effect pre run3 ready3 e3
    (by change ∀ c ∈ [.reg 15, .rip], BodyComponent (rspOf t2) c
        simp [BodyComponent]) (by simp; decide)
  have ptr3 : t3.regValue .rsi = s.regValue .rsi :=
    (f3.read (r := 6) (n := 64) (by simp)).trans ptr2
  have mem3 : t3.external = t1.external :=
    (f3.external (by simp [Component.Covers])).trans mem2
  have v3 : (Operand.reg 15 : Operand 64).read t3 = a.l2 := by
    have h : (Operand.reg 15 : Operand 64).read t3 =
      memLoad t2.external (t2.regValue .rsi + 16#64) 64 := e3.writes
    rw [ptr2, mem2] at h
    rw [h]
    have ha := congrArg Limbs.l2 input1
    simpa [readLimbs, Operand.read] using ha
  obtain ⟨t4, run4, ready4, e4⟩ :=
    (mov_r64_m64_effect_step 0x109557 0x4c (by simp [RexWPrefix]) 2
      (.base 6 .none) (by decide) rfl rfl).advances ready3
      (programText_slice (programLoaded_codeIn st3.loaded) 0x9557 _ (by decide) (by decide +kernel))
      ⟨e3.rip, by
        change MemReadable t3 (t3.regValue .rsi + 0#64) 8
        rw [ptr3]
        exact st3.input_readable pre (offset := 0) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x955a (by decide)))
  have f4 : AgreesExcept [.reg 10, .rip] t3 t4 := e4.agrees
  have st4 := st3.of_effect pre run4 ready4 e4
    (by change ∀ c ∈ [.reg 10, .rip], BodyComponent (rspOf t3) c
        simp [BodyComponent]) (by simp; decide)
  have ptr4 : t4.regValue .rsi = s.regValue .rsi :=
    (f4.read (r := 6) (n := 64) (by simp)).trans ptr3
  have mem4 : t4.external = t1.external :=
    (f4.external (by simp [Component.Covers])).trans mem3
  have v4 : (Operand.reg 10 : Operand 64).read t4 = a.l0 := by
    have h : (Operand.reg 10 : Operand 64).read t4 =
      memLoad t3.external (t3.regValue .rsi + 0#64) 64 := e4.writes
    rw [ptr3, mem3] at h
    rw [h]
    have ha := congrArg Limbs.l0 input1
    simpa [readLimbs, Operand.read] using ha
  obtain ⟨t5, run5, ready5, e5⟩ :=
    (mov_r64_m64_effect_step 0x10955a 0x4c (by simp [RexWPrefix]) 6
      (.base 6 (.d8 8)) (by decide) rfl rfl).advances ready4
      (programText_slice (programLoaded_codeIn st4.loaded) 0x955a _ (by decide) (by decide +kernel))
      ⟨e4.rip, by
        change MemReadable t4 (t4.regValue .rsi + 8#64) 8
        rw [ptr4]
        exact st4.input_readable pre (offset := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x955e (by decide)))
  have f5 : AgreesExcept [.reg 14, .rip] t4 t5 := e5.agrees
  have st5 := st4.of_effect pre run5 ready5 e5
    (by change ∀ c ∈ [.reg 14, .rip], BodyComponent (rspOf t4) c
        simp [BodyComponent]) (by simp; decide)
  have ptr5 : t5.regValue .rsi = s.regValue .rsi :=
    (f5.read (r := 6) (n := 64) (by simp)).trans ptr4
  have mem5 : t5.external = t1.external :=
    (f5.external (by simp [Component.Covers])).trans mem4
  have v5 : (Operand.reg 14 : Operand 64).read t5 = a.l1 := by
    have h : (Operand.reg 14 : Operand 64).read t5 =
      memLoad t4.external (t4.regValue .rsi + 8#64) 64 := e5.writes
    rw [ptr4, mem4] at h
    rw [h]
    have ha := congrArg Limbs.l1 input1
    simpa [readLimbs, Operand.read] using ha
  obtain ⟨t6, run6, ready6, e6⟩ :=
    (mov_r32_r32_effect_step 0x10955e 0xd0 rfl).advances ready5
      (programText_slice (programLoaded_codeIn st5.loaded) 0x955e _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9560 (by decide)))
  have f6 : AgreesExcept [.reg 0, .rip] t5 t6 := e6.agrees
  have st6 := st5.of_effect pre run6 ready6 e6
    (by change ∀ c ∈ [.reg 0, .rip], BodyComponent (rspOf t5) c
        simp [BodyComponent]) (by change Component.reg 4 ∉ [.reg 0, .rip]; simp)
  have mem6 : t6.external = t1.external :=
    (f6.external (by simp [Component.Covers])).trans mem5
  have count5 : t5.regValue .rdx = 0 := by
    change (Operand.reg 2 : Operand 64).read t5 = _
    rw [f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  have v6 : t6.regValue .rax = 0 := by
    have h : t6.regValue .rax = ((t5.regValue .rdx).setWidth 32).setWidth 64 := e6.writes
    rw [count5] at h
    exact h
  obtain ⟨t7, run7, ready7, e7⟩ :=
    (shr_al_six_effect_step 0x109560).advances ready6
      (programText_slice (programLoaded_codeIn st6.loaded) 0x9560 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9563 (by decide)))
  have f7 : AgreesExcept [.reg 0, .flags, .rip] t6 t7 := e7.agrees
  have st7 := st6.of_effect pre run7 ready7 e7
    (by change ∀ c ∈ [.reg 0, .flags, .rip], BodyComponent (rspOf t6) c
        simp [BodyComponent]) (by change Component.reg 4 ∉ [.reg 0, .flags, .rip]; simp)
  have mem7 : t7.external = t1.external :=
    (f7.external (by simp [Component.Covers])).trans mem6
  have v7 : t7.regValue .rax = 0 := by
    have h := e7.writes
    change t7.regValue .rax = mergeGPR 8 ((t6.regValue .rax).setWidth 8 >>> 6) (t6.regValue .rax) at h
    rw [v6] at h
    exact h
  obtain ⟨t8, run8, ready8, e8⟩ :=
    (and_al_imm8_effect_step 0x109563 1).advances ready7
      (programText_slice (programLoaded_codeIn st7.loaded) 0x9563 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9565 (by decide)))
  have f8 : AgreesExcept [.reg 0, .flags, .rip] t7 t8 := e8.agrees
  have st8 := st7.of_effect pre run8 ready8 e8
    (by change ∀ c ∈ [.reg 0, .flags, .rip], BodyComponent (rspOf t7) c
        simp [BodyComponent]) (by change Component.reg 4 ∉ [.reg 0, .flags, .rip]; simp)
  have mem8 : t8.external = t1.external :=
    (f8.external (by simp [Component.Covers])).trans mem7
  have v8 : t8.regValue .rax = 0 := by
    have h := e8.writes
    change t8.regValue .rax = mergeGPR 8 ((t7.regValue .rax).setWidth 8 &&& 1) (t7.regValue .rax) at h
    rw [v7] at h
    exact h
  refine ⟨t8, st8, e8.rip, ?_, ?_, ?_, ?_, ?_, ?_, v8⟩
  · rw [mem8]
    exact saved1
  · change (Operand.reg 2 : Operand 64).read t8 = _
    rw [f8.read (r := 2) (n := 64) (by simp), f7.read (r := 2) (n := 64) (by simp), f6.read (r := 2) (n := 64) (by simp), f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  · change (Operand.reg 13 : Operand 64).read t8 = _
    rw [f8.read (r := 13) (n := 64) (by simp), f7.read (r := 13) (n := 64) (by simp), f6.read (r := 13) (n := 64) (by simp), f5.read (r := 13) (n := 64) (by simp), f4.read (r := 13) (n := 64) (by simp), f3.read (r := 13) (n := 64) (by simp)]
    exact v2
  · change (Operand.reg 15 : Operand 64).read t8 = _
    rw [f8.read (r := 15) (n := 64) (by simp), f7.read (r := 15) (n := 64) (by simp), f6.read (r := 15) (n := 64) (by simp), f5.read (r := 15) (n := 64) (by simp), f4.read (r := 15) (n := 64) (by simp)]
    exact v3
  · change (Operand.reg 10 : Operand 64).read t8 = _
    rw [f8.read (r := 10) (n := 64) (by simp), f7.read (r := 10) (n := 64) (by simp), f6.read (r := 10) (n := 64) (by simp), f5.read (r := 10) (n := 64) (by simp)]
    exact v4
  · change (Operand.reg 14 : Operand 64).read t8 = _
    rw [f8.read (r := 14) (n := 64) (by simp), f7.read (r := 14) (n := 64) (by simp), f6.read (r := 14) (n := 64) (by simp)]
    exact v5

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
