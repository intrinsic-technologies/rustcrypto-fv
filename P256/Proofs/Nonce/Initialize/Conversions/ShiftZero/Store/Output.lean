import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Memory
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem store_memLoad_apart {s t : RamState} {a b : BitVec 64}
    (h : AgreesExcept [.mem a 8, .rip] s t) (apart : RangeApart a 8 b 8) :
    (Operand.mem b : Operand 64).read t = (Operand.mem b : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  apply congrArg (fun o : Option UInt8 => o.getD 0)
  apply h.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hv
    exact apart i hi j hj he.symm
  · exact hv.elim

theorem write_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : OutputState s t boundary a) :
    ∃ u, StoredState s u boundary a := by
  have st0 := state.toStage
  have ready0 := state.ready
  have h1r0 : (Operand.reg 0 : Operand 64).read t = s.regValue .rdi := by
    exact state.rax
  have h1r14 : (Operand.reg 14 : Operand 64).read t = a.l0 := by
    exact state.r14
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x1096c5 0x4c (by simp [RexWPrefix]) 6 (.base 0 .none) (by decide) rfl rfl).advances ready0
      (programText_slice (programLoaded_codeIn st0.loaded) 0x96c5 _ (by decide) (by decide +kernel))
      ⟨state.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t
          ((Operand.reg 0 : Operand 64).read t + 0#64) 8
        rw [h1r0]
        exact output_writable pre st0 (offset := 0) (by decide), by
        change RangeApart ((Operand.reg 0 : Operand 64).read t + 0#64) 8 0x1096c5 3
        rw [h1r0]
        exact output_code_apart pre (offset := 0) (pc := 0x96c5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96c8 (by decide)))
  have f1 : AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .rip] t t1 := by
    have h := e1.agrees
    simp only [movM64R64Effect, storeEffect_components] at h
    change AgreesExcept [.mem ((Operand.reg 0 : Operand 64).read t + 0#64) 8, .rip] t t1 at h
    rwa [h1r0] at h
  have st1 := output_stage pre st0 (offset := 0) (by decide) run1 ready1 f1
  have w1 : memLoad t1.external (s.regValue .rdi + 0#64) 64 = a.l0 := by
    have h : memLoad t1.external ((Operand.reg 0 : Operand 64).read t + 0#64) 64 =
      (Operand.reg 14 : Operand 64).read t := e1.writes
    rwa [h1r0, h1r14] at h
  have h2r0 : (Operand.reg 0 : Operand 64).read t1 = s.regValue .rdi := by
    rw [f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  have h2r3 : (Operand.reg 3 : Operand 64).read t1 = a.l1 := by
    rw [f1.read (r := 3) (n := 64) (by simp)]
    exact state.rbx
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x1096c8 0x48 (by simp [RexWPrefix]) 3 (.base 0 (.d8 8)) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn st1.loaded) 0x96c8 _ (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1
          ((Operand.reg 0 : Operand 64).read t1 + 8#64) 8
        rw [h2r0]
        exact output_writable pre st1 (offset := 8) (by decide), by
        change RangeApart ((Operand.reg 0 : Operand 64).read t1 + 8#64) 8 0x1096c8 4
        rw [h2r0]
        exact output_code_apart pre (offset := 8) (pc := 0x96c8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96cc (by decide)))
  have f2 : AgreesExcept [.mem (s.regValue .rdi + 8#64) 8, .rip] t1 t2 := by
    have h := e2.agrees
    simp only [movM64R64Effect, storeEffect_components] at h
    change AgreesExcept [.mem ((Operand.reg 0 : Operand 64).read t1 + 8#64) 8, .rip] t1 t2 at h
    rwa [h2r0] at h
  have st2 := output_stage pre st1 (offset := 8) (by decide) run2 ready2 f2
  have w2 : memLoad t2.external (s.regValue .rdi + 8#64) 64 = a.l1 := by
    have h : memLoad t2.external ((Operand.reg 0 : Operand 64).read t1 + 8#64) 64 =
      (Operand.reg 3 : Operand 64).read t1 := e2.writes
    rwa [h2r0, h2r3] at h
  have h3r0 : (Operand.reg 0 : Operand 64).read t2 = s.regValue .rdi := by
    rw [f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  have h3r9 : (Operand.reg 9 : Operand 64).read t2 = a.l2 := by
    rw [f2.read (r := 9) (n := 64) (by simp), f1.read (r := 9) (n := 64) (by simp)]
    exact state.r9
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x1096cc 0x4c (by simp [RexWPrefix]) 1 (.base 0 (.d8 16)) (by decide) rfl rfl).advances ready2
      (programText_slice (programLoaded_codeIn st2.loaded) 0x96cc _ (by decide) (by decide +kernel))
      ⟨e2.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t2
          ((Operand.reg 0 : Operand 64).read t2 + 16#64) 8
        rw [h3r0]
        exact output_writable pre st2 (offset := 16) (by decide), by
        change RangeApart ((Operand.reg 0 : Operand 64).read t2 + 16#64) 8 0x1096cc 4
        rw [h3r0]
        exact output_code_apart pre (offset := 16) (pc := 0x96cc) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96d0 (by decide)))
  have f3 : AgreesExcept [.mem (s.regValue .rdi + 16#64) 8, .rip] t2 t3 := by
    have h := e3.agrees
    simp only [movM64R64Effect, storeEffect_components] at h
    change AgreesExcept [.mem ((Operand.reg 0 : Operand 64).read t2 + 16#64) 8, .rip] t2 t3 at h
    rwa [h3r0] at h
  have st3 := output_stage pre st2 (offset := 16) (by decide) run3 ready3 f3
  have w3 : memLoad t3.external (s.regValue .rdi + 16#64) 64 = a.l2 := by
    have h : memLoad t3.external ((Operand.reg 0 : Operand 64).read t2 + 16#64) 64 =
      (Operand.reg 9 : Operand 64).read t2 := e3.writes
    rwa [h3r0, h3r9] at h
  have h4r0 : (Operand.reg 0 : Operand 64).read t3 = s.regValue .rdi := by
    rw [f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  have h4r10 : (Operand.reg 10 : Operand 64).read t3 = a.l3 := by
    rw [f3.read (r := 10) (n := 64) (by simp), f2.read (r := 10) (n := 64) (by simp), f1.read (r := 10) (n := 64) (by simp)]
    exact state.r10
  obtain ⟨t4, run4, ready4, e4⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x1096d0 0x4c (by simp [RexWPrefix]) 2 (.base 0 (.d8 24)) (by decide) rfl rfl).advances ready3
      (programText_slice (programLoaded_codeIn st3.loaded) 0x96d0 _ (by decide) (by decide +kernel))
      ⟨e3.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t3
          ((Operand.reg 0 : Operand 64).read t3 + 24#64) 8
        rw [h4r0]
        exact output_writable pre st3 (offset := 24) (by decide), by
        change RangeApart ((Operand.reg 0 : Operand 64).read t3 + 24#64) 8 0x1096d0 4
        rw [h4r0]
        exact output_code_apart pre (offset := 24) (pc := 0x96d0) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96d4 (by decide)))
  have f4 : AgreesExcept [.mem (s.regValue .rdi + 24#64) 8, .rip] t3 t4 := by
    have h := e4.agrees
    simp only [movM64R64Effect, storeEffect_components] at h
    change AgreesExcept [.mem ((Operand.reg 0 : Operand 64).read t3 + 24#64) 8, .rip] t3 t4 at h
    rwa [h4r0] at h
  have st4 := output_stage pre st3 (offset := 24) (by decide) run4 ready4 f4
  have w4 : memLoad t4.external (s.regValue .rdi + 24#64) 64 = a.l3 := by
    have h : memLoad t4.external ((Operand.reg 0 : Operand 64).read t3 + 24#64) 64 =
      (Operand.reg 10 : Operand 64).read t3 := e4.writes
    rwa [h4r0, h4r10] at h
  have m21 : memLoad t2.external (s.regValue .rdi + 0#64) 64 =
      memLoad t1.external (s.regValue .rdi + 0#64) 64 :=
    store_memLoad_apart f2 (by
      intro i hi j hj
      exact (show OffsetsApart 8 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  have m31 : memLoad t3.external (s.regValue .rdi + 0#64) 64 =
      memLoad t2.external (s.regValue .rdi + 0#64) 64 :=
    store_memLoad_apart f3 (by
      intro i hi j hj
      exact (show OffsetsApart 16 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  have m41 : memLoad t4.external (s.regValue .rdi + 0#64) 64 =
      memLoad t3.external (s.regValue .rdi + 0#64) 64 :=
    store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 0 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  have m32 : memLoad t3.external (s.regValue .rdi + 8#64) 64 =
      memLoad t2.external (s.regValue .rdi + 8#64) 64 :=
    store_memLoad_apart f3 (by
      intro i hi j hj
      exact (show OffsetsApart 16 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  have m42 : memLoad t4.external (s.regValue .rdi + 8#64) 64 =
      memLoad t3.external (s.regValue .rdi + 8#64) 64 :=
    store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 8 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  have m43 : memLoad t4.external (s.regValue .rdi + 16#64) 64 =
      memLoad t3.external (s.regValue .rdi + 16#64) 64 :=
    store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 16 8 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hi hj (by decide))
  refine ⟨t4, st4, e4.rip, ?_⟩
  have represented := nat256At_readLimbs (s := t4) (address := s.regValue .rdi) (by
    intro i hi
    apply st4.agrees.grow
    exact (memoryRegion_memReadable pre.outputBounded pre.outputAllocated
      (Nat.le_refl _) (Nat.le_refl _)).mem i hi)
  have eq : readLimbs t4 (s.regValue .rdi) = a := by
    have h0 := ((m41.trans m31).trans m21).trans w1
    have h1 := (m42.trans m32).trans w2
    have h2 := m43.trans w3
    have h3 := w4
    simp only [BitVec.add_zero] at h0
    change Limbs.mk _ _ _ _ = a
    simp only [BitVec.ofNat_eq_ofNat, h0, h1, h2, h3]

  simpa only [eq] using represented

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store
