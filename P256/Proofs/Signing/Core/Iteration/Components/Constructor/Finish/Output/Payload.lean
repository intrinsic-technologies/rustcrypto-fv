import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.State

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem copy_payload [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109a2c)
    (first : Nat256At t (stackPtr t + 64) x)
    (second : Nat256At t (stackPtr t + 96) y) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x109a7b ∧ Payload u x y := by
  obtain ⟨t1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x109a2c 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x9a2c _
        (by decide) (by decide +kernel))
      ⟨rip, stack_readable pre state.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a31 (by decide)))
  change (movR64M64Effect 0x109a2c 0 (.sib 4 none 0 (.d8 88)) t).Holds t t1 at e1
  have f1 : AgreesExcept [.reg 0, .rip] t t1 := e1.agrees
  have h1 := state.after_registers a1 r1 f1 (by simp [Component.Covers]) (by simp)
  have m1 : t1.external = t.external := f1.external (by simp [Component.Covers])
  have sp1 : stackPtr t1 = stackPtr t := f1.read (n := 64) (r := 4) (by simp)
  have v1 : (Operand.reg 0 : Operand 64).read t1 = BitVec.ofNat 64 (x / 2^192) := by
    have hw : (Operand.reg 0 : Operand 64).read t1 =
        memLoad t.external (stackPtr t + 88#64) 64 := e1.writes
    have hx := first.memLoad_limb 3 (by decide)
    change memLoad t.external (stackPtr t + 64#64 + 24#64) 64 =
      BitVec.ofNat 64 (x / 2^192) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first1 : Nat256At t1 (stackPtr t1 + 64) x := by
    simpa only [Nat256At, m1, sp1, BitVec.ofNat_eq_ofNat] using first
  have second1 : Nat256At t1 (stackPtr t1 + 96) y := by
    simpa only [Nat256At, m1, sp1, BitVec.ofNat_eq_ofNat] using second
  obtain ⟨t2, a2, r2, e2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a31 0x48
      (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances
      (readyToStep h1.machine h1.bindingsSupported)
      (programText_slice (programLoaded_codeIn h1.loaded) 0x9a31 _
        (by decide) (by decide +kernel))
      ⟨e1.rip, stack_writable pre h1.toFrame (by decide) (by decide),
        stack_code pre h1.toFrame (offset := 24) (len := 8) (codeOffset := 0x9a31) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a36 (by decide)))
  have f2 : AgreesExcept [.mem (stackPtr t1 + 24#64) 8, .rip] t1 t2 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have h2 := after_stack_store pre h1 a2 r2 f2 (by decide)
  have first2 := nat256_after_stack_store f2 (by unfold OffsetsApart; decide +kernel) first1
  have second2 := nat256_after_stack_store f2 (by unfold OffsetsApart; decide +kernel) second1
  obtain ⟨t3, a3, r3, e3⟩ :=
    (mov_r64_m64_effect_step 0x109a36 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances
      (readyToStep h2.machine h2.bindingsSupported)
      (programText_slice (programLoaded_codeIn h2.loaded) 0x9a36 _
        (by decide) (by decide +kernel))
      ⟨e2.rip, stack_readable pre h2.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a3b (by decide)))
  change (movR64M64Effect 0x109a36 1 (.sib 4 none 0 (.d8 80)) t2).Holds t2 t3 at e3
  have f3 : AgreesExcept [.reg 1, .rip] t2 t3 := e3.agrees
  have h3 := h2.after_registers a3 r3 f3 (by simp [Component.Covers]) (by simp)
  have m3 : t3.external = t2.external := f3.external (by simp [Component.Covers])
  have sp3 : stackPtr t3 = stackPtr t2 := f3.read (n := 64) (r := 4) (by simp)
  have v3 : (Operand.reg 1 : Operand 64).read t3 = BitVec.ofNat 64 (x / 2^128) := by
    have hw : (Operand.reg 1 : Operand 64).read t3 =
        memLoad t2.external (stackPtr t2 + 80#64) 64 := e3.writes
    have hx := first2.memLoad_limb 2 (by decide)
    change memLoad t2.external (stackPtr t2 + 64#64 + 16#64) 64 =
      BitVec.ofNat 64 (x / 2^128) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first3 : Nat256At t3 (stackPtr t3 + 64) x := by
    simpa only [Nat256At, m3, sp3, BitVec.ofNat_eq_ofNat] using first2
  have second3 : Nat256At t3 (stackPtr t3 + 96) y := by
    simpa only [Nat256At, m3, sp3, BitVec.ofNat_eq_ofNat] using second2
  obtain ⟨t4, a4, r4, e4⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a3b 0x48
      (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances
      (readyToStep h3.machine h3.bindingsSupported)
      (programText_slice (programLoaded_codeIn h3.loaded) 0x9a3b _
        (by decide) (by decide +kernel))
      ⟨e3.rip, stack_writable pre h3.toFrame (by decide) (by decide),
        stack_code pre h3.toFrame (offset := 16) (len := 8) (codeOffset := 0x9a3b) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a40 (by decide)))
  have f4 : AgreesExcept [.mem (stackPtr t3 + 16#64) 8, .rip] t3 t4 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have h4 := after_stack_store pre h3 a4 r4 f4 (by decide)
  have first4 := nat256_after_stack_store f4 (by unfold OffsetsApart; decide +kernel) first3
  have second4 := nat256_after_stack_store f4 (by unfold OffsetsApart; decide +kernel) second3
  obtain ⟨t5, a5, r5, e5⟩ :=
    (mov_r64_m64_effect_step 0x109a40 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl).advances
      (readyToStep h4.machine h4.bindingsSupported)
      (programText_slice (programLoaded_codeIn h4.loaded) 0x9a40 _
        (by decide) (by decide +kernel))
      ⟨e4.rip, stack_readable pre h4.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a45 (by decide)))
  change (movR64M64Effect 0x109a40 2 (.sib 4 none 0 (.d8 64)) t4).Holds t4 t5 at e5
  have f5 : AgreesExcept [.reg 2, .rip] t4 t5 := e5.agrees
  have h5 := h4.after_registers a5 r5 f5 (by simp [Component.Covers]) (by simp)
  have m5 : t5.external = t4.external := f5.external (by simp [Component.Covers])
  have sp5 : stackPtr t5 = stackPtr t4 := f5.read (n := 64) (r := 4) (by simp)
  have v5 : (Operand.reg 2 : Operand 64).read t5 = BitVec.ofNat 64 (x / 2^0) := by
    have hw : (Operand.reg 2 : Operand 64).read t5 =
        memLoad t4.external (stackPtr t4 + 64#64) 64 := e5.writes
    have hx := first4.memLoad_limb 0 (by decide)
    change memLoad t4.external (stackPtr t4 + 64#64 + 0#64) 64 =
      BitVec.ofNat 64 (x / 2^0) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first5 : Nat256At t5 (stackPtr t5 + 64) x := by
    simpa only [Nat256At, m5, sp5, BitVec.ofNat_eq_ofNat] using first4
  have second5 : Nat256At t5 (stackPtr t5 + 96) y := by
    simpa only [Nat256At, m5, sp5, BitVec.ofNat_eq_ofNat] using second4
  obtain ⟨t6, a6, r6, e6⟩ :=
    (mov_r64_m64_effect_step 0x109a45 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl).advances
      (readyToStep h5.machine h5.bindingsSupported)
      (programText_slice (programLoaded_codeIn h5.loaded) 0x9a45 _
        (by decide) (by decide +kernel))
      ⟨e5.rip, stack_readable pre h5.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a4a (by decide)))
  change (movR64M64Effect 0x109a45 6 (.sib 4 none 0 (.d8 72)) t5).Holds t5 t6 at e6
  have f6 : AgreesExcept [.reg 6, .rip] t5 t6 := e6.agrees
  have h6 := h5.after_registers a6 r6 f6 (by simp [Component.Covers]) (by simp)
  have m6 : t6.external = t5.external := f6.external (by simp [Component.Covers])
  have sp6 : stackPtr t6 = stackPtr t5 := f6.read (n := 64) (r := 4) (by simp)
  have v6 : (Operand.reg 6 : Operand 64).read t6 = BitVec.ofNat 64 (x / 2^64) := by
    have hw : (Operand.reg 6 : Operand 64).read t6 =
        memLoad t5.external (stackPtr t5 + 72#64) 64 := e6.writes
    have hx := first5.memLoad_limb 1 (by decide)
    change memLoad t5.external (stackPtr t5 + 64#64 + 8#64) 64 =
      BitVec.ofNat 64 (x / 2^64) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first6 : Nat256At t6 (stackPtr t6 + 64) x := by
    simpa only [Nat256At, m6, sp6, BitVec.ofNat_eq_ofNat] using first5
  have second6 : Nat256At t6 (stackPtr t6 + 96) y := by
    simpa only [Nat256At, m6, sp6, BitVec.ofNat_eq_ofNat] using second5
  obtain ⟨t7, a7, r7, e7⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a4a 0x48
      (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances
      (readyToStep h6.machine h6.bindingsSupported)
      (programText_slice (programLoaded_codeIn h6.loaded) 0x9a4a _
        (by decide) (by decide +kernel))
      ⟨e6.rip, stack_writable pre h6.toFrame (by decide) (by decide),
        stack_code pre h6.toFrame (offset := 8) (len := 8) (codeOffset := 0x9a4a) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a4f (by decide)))
  have f7 : AgreesExcept [.mem (stackPtr t6 + 8#64) 8, .rip] t6 t7 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have h7 := after_stack_store pre h6 a7 r7 f7 (by decide)
  have first7 := nat256_after_stack_store f7 (by unfold OffsetsApart; decide +kernel) first6
  have second7 := nat256_after_stack_store f7 (by unfold OffsetsApart; decide +kernel) second6
  obtain ⟨t8, a8, r8, e8⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a4f 0x48
      (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide) rfl rfl).advances
      (readyToStep h7.machine h7.bindingsSupported)
      (programText_slice (programLoaded_codeIn h7.loaded) 0x9a4f _
        (by decide) (by decide +kernel))
      ⟨e7.rip, stack_writable pre h7.toFrame (by decide) (by decide),
        stack_code pre h7.toFrame (offset := 0) (len := 8) (codeOffset := 0x9a4f) (codeLen := 4) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a53 (by decide)))
  have f8 : AgreesExcept [.mem (stackPtr t7 + 0#64) 8, .rip] t7 t8 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e8.agrees
  have h8 := after_stack_store pre h7 a8 r8 f8 (by decide)
  have first8 := nat256_after_stack_store f8 (by unfold OffsetsApart; decide +kernel) first7
  have second8 := nat256_after_stack_store f8 (by unfold OffsetsApart; decide +kernel) second7
  obtain ⟨t9, a9, r9, e9⟩ :=
    (mov_r64_m64_effect_step 0x109a53 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl).advances
      (readyToStep h8.machine h8.bindingsSupported)
      (programText_slice (programLoaded_codeIn h8.loaded) 0x9a53 _
        (by decide) (by decide +kernel))
      ⟨e8.rip, stack_readable pre h8.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a58 (by decide)))
  change (movR64M64Effect 0x109a53 7 (.sib 4 none 0 (.d8 96)) t8).Holds t8 t9 at e9
  have f9 : AgreesExcept [.reg 7, .rip] t8 t9 := e9.agrees
  have h9 := h8.after_registers a9 r9 f9 (by simp [Component.Covers]) (by simp)
  have m9 : t9.external = t8.external := f9.external (by simp [Component.Covers])
  have sp9 : stackPtr t9 = stackPtr t8 := f9.read (n := 64) (r := 4) (by simp)
  have v9 : (Operand.reg 7 : Operand 64).read t9 = BitVec.ofNat 64 (y / 2^0) := by
    have hw : (Operand.reg 7 : Operand 64).read t9 =
        memLoad t8.external (stackPtr t8 + 96#64) 64 := e9.writes
    have hx := second8.memLoad_limb 0 (by decide)
    change memLoad t8.external (stackPtr t8 + 96#64 + 0#64) 64 =
      BitVec.ofNat 64 (y / 2^0) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first9 : Nat256At t9 (stackPtr t9 + 64) x := by
    simpa only [Nat256At, m9, sp9, BitVec.ofNat_eq_ofNat] using first8
  have second9 : Nat256At t9 (stackPtr t9 + 96) y := by
    simpa only [Nat256At, m9, sp9, BitVec.ofNat_eq_ofNat] using second8
  obtain ⟨t10, a10, r10, e10⟩ :=
    (mov_r64_m64_effect_step 0x109a58 0x4c (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl).advances
      (readyToStep h9.machine h9.bindingsSupported)
      (programText_slice (programLoaded_codeIn h9.loaded) 0x9a58 _
        (by decide) (by decide +kernel))
      ⟨e9.rip, stack_readable pre h9.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a5d (by decide)))
  change (movR64M64Effect 0x109a58 8 (.sib 4 none 0 (.d8 104)) t9).Holds t9 t10 at e10
  have f10 : AgreesExcept [.reg 8, .rip] t9 t10 := e10.agrees
  have h10 := h9.after_registers a10 r10 f10 (by simp [Component.Covers]) (by simp)
  have m10 : t10.external = t9.external := f10.external (by simp [Component.Covers])
  have sp10 : stackPtr t10 = stackPtr t9 := f10.read (n := 64) (r := 4) (by simp)
  have v10 : (Operand.reg 8 : Operand 64).read t10 = BitVec.ofNat 64 (y / 2^64) := by
    have hw : (Operand.reg 8 : Operand 64).read t10 =
        memLoad t9.external (stackPtr t9 + 104#64) 64 := e10.writes
    have hx := second9.memLoad_limb 1 (by decide)
    change memLoad t9.external (stackPtr t9 + 96#64 + 8#64) 64 =
      BitVec.ofNat 64 (y / 2^64) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first10 : Nat256At t10 (stackPtr t10 + 64) x := by
    simpa only [Nat256At, m10, sp10, BitVec.ofNat_eq_ofNat] using first9
  have second10 : Nat256At t10 (stackPtr t10 + 96) y := by
    simpa only [Nat256At, m10, sp10, BitVec.ofNat_eq_ofNat] using second9
  obtain ⟨t11, a11, r11, e11⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a5d 0x48
      (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances
      (readyToStep h10.machine h10.bindingsSupported)
      (programText_slice (programLoaded_codeIn h10.loaded) 0x9a5d _
        (by decide) (by decide +kernel))
      ⟨e10.rip, stack_writable pre h10.toFrame (by decide) (by decide),
        stack_code pre h10.toFrame (offset := 32) (len := 8) (codeOffset := 0x9a5d) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a62 (by decide)))
  have f11 : AgreesExcept [.mem (stackPtr t10 + 32#64) 8, .rip] t10 t11 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e11.agrees
  have h11 := after_stack_store pre h10 a11 r11 f11 (by decide)
  have first11 := nat256_after_stack_store f11 (by unfold OffsetsApart; decide +kernel) first10
  have second11 := nat256_after_stack_store f11 (by unfold OffsetsApart; decide +kernel) second10
  obtain ⟨t12, a12, r12, e12⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a62 0x4c
      (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances
      (readyToStep h11.machine h11.bindingsSupported)
      (programText_slice (programLoaded_codeIn h11.loaded) 0x9a62 _
        (by decide) (by decide +kernel))
      ⟨e11.rip, stack_writable pre h11.toFrame (by decide) (by decide),
        stack_code pre h11.toFrame (offset := 40) (len := 8) (codeOffset := 0x9a62) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a67 (by decide)))
  have f12 : AgreesExcept [.mem (stackPtr t11 + 40#64) 8, .rip] t11 t12 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e12.agrees
  have h12 := after_stack_store pre h11 a12 r12 f12 (by decide)
  have first12 := nat256_after_stack_store f12 (by unfold OffsetsApart; decide +kernel) first11
  have second12 := nat256_after_stack_store f12 (by unfold OffsetsApart; decide +kernel) second11
  obtain ⟨t13, a13, r13, e13⟩ :=
    (mov_r64_m64_effect_step 0x109a67 0x4c (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl).advances
      (readyToStep h12.machine h12.bindingsSupported)
      (programText_slice (programLoaded_codeIn h12.loaded) 0x9a67 _
        (by decide) (by decide +kernel))
      ⟨e12.rip, stack_readable pre h12.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a6c (by decide)))
  change (movR64M64Effect 0x109a67 9 (.sib 4 none 0 (.d8 112)) t12).Holds t12 t13 at e13
  have f13 : AgreesExcept [.reg 9, .rip] t12 t13 := e13.agrees
  have h13 := h12.after_registers a13 r13 f13 (by simp [Component.Covers]) (by simp)
  have m13 : t13.external = t12.external := f13.external (by simp [Component.Covers])
  have sp13 : stackPtr t13 = stackPtr t12 := f13.read (n := 64) (r := 4) (by simp)
  have v13 : (Operand.reg 9 : Operand 64).read t13 = BitVec.ofNat 64 (y / 2^128) := by
    have hw : (Operand.reg 9 : Operand 64).read t13 =
        memLoad t12.external (stackPtr t12 + 112#64) 64 := e13.writes
    have hx := second12.memLoad_limb 2 (by decide)
    change memLoad t12.external (stackPtr t12 + 96#64 + 16#64) 64 =
      BitVec.ofNat 64 (y / 2^128) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first13 : Nat256At t13 (stackPtr t13 + 64) x := by
    simpa only [Nat256At, m13, sp13, BitVec.ofNat_eq_ofNat] using first12
  have second13 : Nat256At t13 (stackPtr t13 + 96) y := by
    simpa only [Nat256At, m13, sp13, BitVec.ofNat_eq_ofNat] using second12
  obtain ⟨t14, a14, r14, e14⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a6c 0x4c
      (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances
      (readyToStep h13.machine h13.bindingsSupported)
      (programText_slice (programLoaded_codeIn h13.loaded) 0x9a6c _
        (by decide) (by decide +kernel))
      ⟨e13.rip, stack_writable pre h13.toFrame (by decide) (by decide),
        stack_code pre h13.toFrame (offset := 48) (len := 8) (codeOffset := 0x9a6c) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a71 (by decide)))
  have f14 : AgreesExcept [.mem (stackPtr t13 + 48#64) 8, .rip] t13 t14 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e14.agrees
  have h14 := after_stack_store pre h13 a14 r14 f14 (by decide)
  have first14 := nat256_after_stack_store f14 (by unfold OffsetsApart; decide +kernel) first13
  have second14 := nat256_after_stack_store f14 (by unfold OffsetsApart; decide +kernel) second13
  obtain ⟨t15, a15, r15, e15⟩ :=
    (mov_r64_m64_effect_step 0x109a71 0x4c (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances
      (readyToStep h14.machine h14.bindingsSupported)
      (programText_slice (programLoaded_codeIn h14.loaded) 0x9a71 _
        (by decide) (by decide +kernel))
      ⟨e14.rip, stack_readable pre h14.toFrame (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a76 (by decide)))
  change (movR64M64Effect 0x109a71 10 (.sib 4 none 0 (.d8 120)) t14).Holds t14 t15 at e15
  have f15 : AgreesExcept [.reg 10, .rip] t14 t15 := e15.agrees
  have h15 := h14.after_registers a15 r15 f15 (by simp [Component.Covers]) (by simp)
  have m15 : t15.external = t14.external := f15.external (by simp [Component.Covers])
  have sp15 : stackPtr t15 = stackPtr t14 := f15.read (n := 64) (r := 4) (by simp)
  have v15 : (Operand.reg 10 : Operand 64).read t15 = BitVec.ofNat 64 (y / 2^192) := by
    have hw : (Operand.reg 10 : Operand 64).read t15 =
        memLoad t14.external (stackPtr t14 + 120#64) 64 := e15.writes
    have hx := second14.memLoad_limb 3 (by decide)
    change memLoad t14.external (stackPtr t14 + 96#64 + 24#64) 64 =
      BitVec.ofNat 64 (y / 2^192) at hx
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx
    exact hw.trans hx
  have first15 : Nat256At t15 (stackPtr t15 + 64) x := by
    simpa only [Nat256At, m15, sp15, BitVec.ofNat_eq_ofNat] using first14
  have second15 : Nat256At t15 (stackPtr t15 + 96) y := by
    simpa only [Nat256At, m15, sp15, BitVec.ofNat_eq_ofNat] using second14
  obtain ⟨t16, a16, r16, e16⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a76 0x4c
      (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances
      (readyToStep h15.machine h15.bindingsSupported)
      (programText_slice (programLoaded_codeIn h15.loaded) 0x9a76 _
        (by decide) (by decide +kernel))
      ⟨e15.rip, stack_writable pre h15.toFrame (by decide) (by decide),
        stack_code pre h15.toFrame (offset := 56) (len := 8) (codeOffset := 0x9a76) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a7b (by decide)))
  have f16 : AgreesExcept [.mem (stackPtr t15 + 56#64) 8, .rip] t15 t16 := by
    simpa [movM64R64Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.offset, AddrMode.reg64, Disp.value, stackPtr] using e16.agrees
  have h16 := after_stack_store pre h15 a16 r16 f16 (by decide)
  refine ⟨t16, h16, e16.rip, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((((((((f2.trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 0) (by simp)).trans v1
  · exact (((((((((((((f4.trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 1) (by simp)).trans v3
  · exact (((((((((((f6.trans f7).trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 2) (by simp)).trans v5
  · exact ((((((((((f7.trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 6) (by simp)).trans v6
  · exact (((((((f10.trans f11).trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 7) (by simp)).trans v9
  · exact ((((((f11.trans f12).trans f13).trans f14).trans f15).trans f16).read (n := 64) (r := 8) (by simp)).trans v10
  · exact (((f14.trans f15).trans f16).read (n := 64) (r := 9) (by simp)).trans v13
  · exact (f16.read (n := 64) (r := 10) (by simp)).trans v15

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
