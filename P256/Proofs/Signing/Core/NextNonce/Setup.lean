import P256.Proofs.Signing.Core.NextNonce.Memory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.NextNonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    (pre : SignPre s boundary) (input : Loop s t state) (rip : t.RIP = 0x10caa5) :
    ∃ u, Advances boundary 7 t u ∧ Loop s u state ∧ u.RIP = 0x10cad4 ∧
      u.regValue .rdx = 32 ∧ u.regValue .rsi = frameBase s + 40 ∧
      u.regValue .rdi = frameBase s + 2160 := by
  have writable1 : MemWritable t (stackPtr t + 64) 8 := by
    rw [input.frame.rsp]
    have address : frameBase s + 64 = stackPtr s - 2216 := base_add s (offset := 64) (by decide)
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) input.frame.allocated
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_m64_imm32_effect_step 0x10caa5 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl 0).advances
      (readyToStep input.frame.machine input.frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.frame.loaded) 0xcaa5 _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, writable1, by
        intro i hi j hj eq
        change stackPtr t + 64 + BitVec.ofNat 64 i = _ at eq
        change j < 9 at hj
        apply pre.avoids (Stack.region s 4584) (by simp)
          (stackPtr t + 64 + BitVec.ofNat 64 i) ?_ (.inl ?_)
        · rw [input.frame.rsp, show frameBase s + 64 = stackPtr s - 2216 from base_add s (offset := 64) (by decide)]
          exact ScalarFrame.stack_contains pre.toCalleePre (offset := 2216) (len := 8)
            (by decide) (by decide) ⟨i, hi, rfl⟩
        · rw [eq]
          have h := inProgram_of_textOffset (0xcaa5 + j) (by omega)
          rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
          exact h⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcaae (by decide)))
  have g1 : AgreesExcept [.mem (stackPtr t + 64) 8, .rip] t s1 := by
    simpa [movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr,
      AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := loop_after_agrees pre input r1 g1 (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      refine ⟨64 + i, by omega, by omega, ?_⟩
      rw [input.frame.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · exact cover.elim) (by simp) (by simp) (by simp) (by simp)
  have writable2 : MemWritable s1 (stackPtr s1 + 56) 8 := by
    rw [f1.frame.rsp]
    have address : frameBase s + 56 = stackPtr s - 2224 := base_add s (offset := 56) (by decide)
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) f1.frame.allocated
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_imm32_effect_step 0x10caae 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl 0).advances
      (readyToStep f1.frame.machine f1.frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.frame.loaded) 0xcaae _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, writable2, by
        intro i hi j hj eq
        change stackPtr s1 + 56 + BitVec.ofNat 64 i = _ at eq
        change j < 9 at hj
        apply pre.avoids (Stack.region s 4584) (by simp)
          (stackPtr s1 + 56 + BitVec.ofNat 64 i) ?_ (.inl ?_)
        · rw [f1.frame.rsp, show frameBase s + 56 = stackPtr s - 2224 from base_add s (offset := 56) (by decide)]
          exact ScalarFrame.stack_contains pre.toCalleePre (offset := 2224) (len := 8)
            (by decide) (by decide) ⟨i, hi, rfl⟩
        · rw [eq]
          have h := inProgram_of_textOffset (0xcaae + j) (by omega)
          rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
          exact h⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcab7 (by decide)))
  have g2 : AgreesExcept [.mem (stackPtr s1 + 56) 8, .rip] s1 s2 := by
    simpa [movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr,
      AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := loop_after_agrees pre f1 r2 g2 (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      refine ⟨56 + i, by omega, by omega, ?_⟩
      rw [f1.frame.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · exact cover.elim) (by simp) (by simp) (by simp) (by simp)
  have writable3 : MemWritable s2 (stackPtr s2 + 48) 8 := by
    rw [f2.frame.rsp]
    have address : frameBase s + 48 = stackPtr s - 2232 := base_add s (offset := 48) (by decide)
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) f2.frame.allocated
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m64_imm32_effect_step 0x10cab7 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 0).advances
      (readyToStep f2.frame.machine f2.frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.frame.loaded) 0xcab7 _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, writable3, by
        intro i hi j hj eq
        change stackPtr s2 + 48 + BitVec.ofNat 64 i = _ at eq
        change j < 9 at hj
        apply pre.avoids (Stack.region s 4584) (by simp)
          (stackPtr s2 + 48 + BitVec.ofNat 64 i) ?_ (.inl ?_)
        · rw [f2.frame.rsp, show frameBase s + 48 = stackPtr s - 2232 from base_add s (offset := 48) (by decide)]
          exact ScalarFrame.stack_contains pre.toCalleePre (offset := 2232) (len := 8)
            (by decide) (by decide) ⟨i, hi, rfl⟩
        · rw [eq]
          have h := inProgram_of_textOffset (0xcab7 + j) (by omega)
          rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
          exact h⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcac0 (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 48) 8, .rip] s2 s3 := by
    simpa [movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr,
      AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := loop_after_agrees pre f2 r3 g3 (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      refine ⟨48 + i, by omega, by omega, ?_⟩
      rw [f2.frame.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · exact cover.elim) (by simp) (by simp) (by simp) (by simp)
  have writable4 : MemWritable s3 (stackPtr s3 + 40) 8 := by
    rw [f3.frame.rsp]
    have address : frameBase s + 40 = stackPtr s - 2240 := base_add s (offset := 40) (by decide)
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) f3.frame.allocated
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_m64_imm32_effect_step 0x10cac0 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 0).advances
      (readyToStep f3.frame.machine f3.frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.frame.loaded) 0xcac0 _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, writable4, by
        intro i hi j hj eq
        change stackPtr s3 + 40 + BitVec.ofNat 64 i = _ at eq
        change j < 9 at hj
        apply pre.avoids (Stack.region s 4584) (by simp)
          (stackPtr s3 + 40 + BitVec.ofNat 64 i) ?_ (.inl ?_)
        · rw [f3.frame.rsp, show frameBase s + 40 = stackPtr s - 2240 from base_add s (offset := 40) (by decide)]
          exact ScalarFrame.stack_contains pre.toCalleePre (offset := 2240) (len := 8)
            (by decide) (by decide) ⟨i, hi, rfl⟩
        · rw [eq]
          have h := inProgram_of_textOffset (0xcac0 + j) (by omega)
          rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
          exact h⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcac9 (by decide)))
  have g4 : AgreesExcept [.mem (stackPtr s3 + 40) 8, .rip] s3 s4 := by
    simpa [movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr,
      AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := loop_after_agrees pre f3 r4 g4 (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      refine ⟨40 + i, by omega, by omega, ?_⟩
      rw [f3.frame.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · exact cover.elim) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨s5, a5, r5, e5⟩ := (mov_r32_imm32_effect_step 0x10cac9 0xba (by decide) 32).advances
    (readyToStep f4.frame.machine f4.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn f4.frame.loaded) 0xcac9 _
      (by decide +kernel) (by decide +kernel)) e4.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcace (by decide)))
  have g5 : AgreesExcept [.reg 2, .rip] s4 s5 := e5.agrees
  have f5 := loop_after_agrees pre f4 r5 g5 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨s6, a6, r6, e6⟩ := (mov_r64_r64_effect_step 0x10cace 0x4c 0xf7 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f5.frame.machine f5.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn f5.frame.loaded) 0xcace _
      (by decide +kernel) (by decide +kernel)) e5.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcad1 (by decide)))
  have g6 : AgreesExcept [.reg 7, .rip] s5 s6 := e6.agrees
  have f6 := loop_after_agrees pre f5 r6 g6 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨u, a7, r7, e7⟩ := (mov_r64_r64_effect_step 0x10cad1 0x48 0xde (by simp [RexWPrefix]) rfl).advances
    (readyToStep f6.frame.machine f6.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.frame.loaded) 0xcad1 _
      (by decide +kernel) (by decide +kernel)) e6.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcad4 (by decide)))
  have g7 : AgreesExcept [.reg 6, .rip] s6 u := e7.agrees
  have f7 := loop_after_agrees pre f6 r7 g7 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  exact ⟨u, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    f7, e7.rip, (g7.read (n := 64) (r := 2) (by simp)).trans
      ((g6.read (n := 64) (r := 2) (by simp)).trans e5.writes),
    e7.writes.trans f6.rbx,
    (g7.read (n := 64) (r := 7) (by simp)).trans (e6.writes.trans f5.r14)⟩

end P256.Proofs.Signing.Core.NextNonce
