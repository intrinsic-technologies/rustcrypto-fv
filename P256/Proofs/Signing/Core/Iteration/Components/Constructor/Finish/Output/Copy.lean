import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.Payload

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem copy_scalars [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109a2c)
    (first : Nat256At t (stackPtr t + 64) x)
    (second : Nat256At t (stackPtr t + 96) y) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x109a9b ∧
      Nat256At u (s.regValue .rdi + 8) x ∧ Nat256At u (s.regValue .rdi + 40) y := by
  obtain ⟨t0, h0, ip0, payload0⟩ := copy_payload pre state rip first second
  obtain ⟨t1, a1, r1, e1⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a7b 0x4c
      (by simp [RexWPrefix]) 2 (.base 3 (.d8 64)) (by decide) rfl rfl).advances
      (readyToStep h0.machine h0.bindingsSupported)
      (programText_slice (programLoaded_codeIn h0.loaded) 0x9a7b _
        (by decide) (by decide +kernel))
      ⟨ip0, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t0 (t0.regValue .rbx + 64#64) 8
        rw [h0.output]
        exact (output_writable pre h0.toFrame).add 64 (by decide), by
        change RangeApart (t0.regValue .rbx + 64#64) 8 0x109a7b 4
        rw [h0.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a7b) (len := 4) (by decide)) 64 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a7f (by decide)))
  change (movM64R64Effect 0x109a7b 10 (.base 3 (.d8 64)) t0).Holds t0 t1 at e1
  have f1 : AgreesExcept [.mem (s.regValue .rdi + 64#64) 8, .rip] t0 t1 := by
    have address (v : RamState) : storeAddrAt 0x109a7b (.base 3 (.d8 64)) 4 v = v.regValue .rbx + 64#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a7b (.base 3 (.d8 64)) 4 t0) 8, .rip] t0 t1 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e1.agrees
    simpa only [address, h0.output] using hf
  have h1 := after_output_store pre h0 a1 r1 f1 (by decide)
  have payload1 := payload0.of_agrees f1 (by simp)
  have v1 : memLoad t1.external (s.regValue .rdi + 64#64) 64 = BitVec.ofNat 64 (y / 2^192) := by
    have hw : memLoad t1.external (t0.regValue .rbx + 64#64) 64 =
        (Operand.reg 10 : Operand 64).read t0 := e1.writes
    rw [h0.output] at hw
    exact hw.trans payload0.r10
  obtain ⟨t2, a2, r2, e2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a7f 0x4c
      (by simp [RexWPrefix]) 1 (.base 3 (.d8 56)) (by decide) rfl rfl).advances
      (readyToStep h1.machine h1.bindingsSupported)
      (programText_slice (programLoaded_codeIn h1.loaded) 0x9a7f _
        (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1 (t1.regValue .rbx + 56#64) 8
        rw [h1.output]
        exact (output_writable pre h1.toFrame).add 56 (by decide), by
        change RangeApart (t1.regValue .rbx + 56#64) 8 0x109a7f 4
        rw [h1.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a7f) (len := 4) (by decide)) 56 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a83 (by decide)))
  change (movM64R64Effect 0x109a7f 9 (.base 3 (.d8 56)) t1).Holds t1 t2 at e2
  have f2 : AgreesExcept [.mem (s.regValue .rdi + 56#64) 8, .rip] t1 t2 := by
    have address (v : RamState) : storeAddrAt 0x109a7f (.base 3 (.d8 56)) 4 v = v.regValue .rbx + 56#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a7f (.base 3 (.d8 56)) 4 t1) 8, .rip] t1 t2 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e2.agrees
    simpa only [address, h1.output] using hf
  have h2 := after_output_store pre h1 a2 r2 f2 (by decide)
  have payload2 := payload1.of_agrees f2 (by simp)
  have v2 : memLoad t2.external (s.regValue .rdi + 56#64) 64 = BitVec.ofNat 64 (y / 2^128) := by
    have hw : memLoad t2.external (t1.regValue .rbx + 56#64) 64 =
        (Operand.reg 9 : Operand 64).read t1 := e2.writes
    rw [h1.output] at hw
    exact hw.trans payload1.r9
  obtain ⟨t3, a3, r3, e3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a83 0x4c
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 48)) (by decide) rfl rfl).advances
      (readyToStep h2.machine h2.bindingsSupported)
      (programText_slice (programLoaded_codeIn h2.loaded) 0x9a83 _
        (by decide) (by decide +kernel))
      ⟨e2.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t2 (t2.regValue .rbx + 48#64) 8
        rw [h2.output]
        exact (output_writable pre h2.toFrame).add 48 (by decide), by
        change RangeApart (t2.regValue .rbx + 48#64) 8 0x109a83 4
        rw [h2.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a83) (len := 4) (by decide)) 48 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a87 (by decide)))
  change (movM64R64Effect 0x109a83 8 (.base 3 (.d8 48)) t2).Holds t2 t3 at e3
  have f3 : AgreesExcept [.mem (s.regValue .rdi + 48#64) 8, .rip] t2 t3 := by
    have address (v : RamState) : storeAddrAt 0x109a83 (.base 3 (.d8 48)) 4 v = v.regValue .rbx + 48#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a83 (.base 3 (.d8 48)) 4 t2) 8, .rip] t2 t3 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e3.agrees
    simpa only [address, h2.output] using hf
  have h3 := after_output_store pre h2 a3 r3 f3 (by decide)
  have payload3 := payload2.of_agrees f3 (by simp)
  have v3 : memLoad t3.external (s.regValue .rdi + 48#64) 64 = BitVec.ofNat 64 (y / 2^64) := by
    have hw : memLoad t3.external (t2.regValue .rbx + 48#64) 64 =
        (Operand.reg 8 : Operand 64).read t2 := e3.writes
    rw [h2.output] at hw
    exact hw.trans payload2.r8
  obtain ⟨t4, a4, r4, e4⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a87 0x48
      (by simp [RexWPrefix]) 7 (.base 3 (.d8 40)) (by decide) rfl rfl).advances
      (readyToStep h3.machine h3.bindingsSupported)
      (programText_slice (programLoaded_codeIn h3.loaded) 0x9a87 _
        (by decide) (by decide +kernel))
      ⟨e3.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t3 (t3.regValue .rbx + 40#64) 8
        rw [h3.output]
        exact (output_writable pre h3.toFrame).add 40 (by decide), by
        change RangeApart (t3.regValue .rbx + 40#64) 8 0x109a87 4
        rw [h3.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a87) (len := 4) (by decide)) 40 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a8b (by decide)))
  change (movM64R64Effect 0x109a87 7 (.base 3 (.d8 40)) t3).Holds t3 t4 at e4
  have f4 : AgreesExcept [.mem (s.regValue .rdi + 40#64) 8, .rip] t3 t4 := by
    have address (v : RamState) : storeAddrAt 0x109a87 (.base 3 (.d8 40)) 4 v = v.regValue .rbx + 40#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a87 (.base 3 (.d8 40)) 4 t3) 8, .rip] t3 t4 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e4.agrees
    simpa only [address, h3.output] using hf
  have h4 := after_output_store pre h3 a4 r4 f4 (by decide)
  have payload4 := payload3.of_agrees f4 (by simp)
  have v4 : memLoad t4.external (s.regValue .rdi + 40#64) 64 = BitVec.ofNat 64 (y / 2^0) := by
    have hw : memLoad t4.external (t3.regValue .rbx + 40#64) 64 =
        (Operand.reg 7 : Operand 64).read t3 := e4.writes
    rw [h3.output] at hw
    exact hw.trans payload3.rdi
  obtain ⟨t5, a5, r5, e5⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a8b 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide) rfl rfl).advances
      (readyToStep h4.machine h4.bindingsSupported)
      (programText_slice (programLoaded_codeIn h4.loaded) 0x9a8b _
        (by decide) (by decide +kernel))
      ⟨e4.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t4 (t4.regValue .rbx + 32#64) 8
        rw [h4.output]
        exact (output_writable pre h4.toFrame).add 32 (by decide), by
        change RangeApart (t4.regValue .rbx + 32#64) 8 0x109a8b 4
        rw [h4.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a8b) (len := 4) (by decide)) 32 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a8f (by decide)))
  change (movM64R64Effect 0x109a8b 0 (.base 3 (.d8 32)) t4).Holds t4 t5 at e5
  have f5 : AgreesExcept [.mem (s.regValue .rdi + 32#64) 8, .rip] t4 t5 := by
    have address (v : RamState) : storeAddrAt 0x109a8b (.base 3 (.d8 32)) 4 v = v.regValue .rbx + 32#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a8b (.base 3 (.d8 32)) 4 t4) 8, .rip] t4 t5 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e5.agrees
    simpa only [address, h4.output] using hf
  have h5 := after_output_store pre h4 a5 r5 f5 (by decide)
  have payload5 := payload4.of_agrees f5 (by simp)
  have v5 : memLoad t5.external (s.regValue .rdi + 32#64) 64 = BitVec.ofNat 64 (x / 2^192) := by
    have hw : memLoad t5.external (t4.regValue .rbx + 32#64) 64 =
        (Operand.reg 0 : Operand 64).read t4 := e5.writes
    rw [h4.output] at hw
    exact hw.trans payload4.rax
  obtain ⟨t6, a6, r6, e6⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a8f 0x48
      (by simp [RexWPrefix]) 1 (.base 3 (.d8 24)) (by decide) rfl rfl).advances
      (readyToStep h5.machine h5.bindingsSupported)
      (programText_slice (programLoaded_codeIn h5.loaded) 0x9a8f _
        (by decide) (by decide +kernel))
      ⟨e5.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t5 (t5.regValue .rbx + 24#64) 8
        rw [h5.output]
        exact (output_writable pre h5.toFrame).add 24 (by decide), by
        change RangeApart (t5.regValue .rbx + 24#64) 8 0x109a8f 4
        rw [h5.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a8f) (len := 4) (by decide)) 24 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a93 (by decide)))
  change (movM64R64Effect 0x109a8f 1 (.base 3 (.d8 24)) t5).Holds t5 t6 at e6
  have f6 : AgreesExcept [.mem (s.regValue .rdi + 24#64) 8, .rip] t5 t6 := by
    have address (v : RamState) : storeAddrAt 0x109a8f (.base 3 (.d8 24)) 4 v = v.regValue .rbx + 24#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a8f (.base 3 (.d8 24)) 4 t5) 8, .rip] t5 t6 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e6.agrees
    simpa only [address, h5.output] using hf
  have h6 := after_output_store pre h5 a6 r6 f6 (by decide)
  have payload6 := payload5.of_agrees f6 (by simp)
  have v6 : memLoad t6.external (s.regValue .rdi + 24#64) 64 = BitVec.ofNat 64 (x / 2^128) := by
    have hw : memLoad t6.external (t5.regValue .rbx + 24#64) 64 =
        (Operand.reg 1 : Operand 64).read t5 := e6.writes
    rw [h5.output] at hw
    exact hw.trans payload5.rcx
  obtain ⟨t7, a7, r7, e7⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a93 0x48
      (by simp [RexWPrefix]) 6 (.base 3 (.d8 16)) (by decide) rfl rfl).advances
      (readyToStep h6.machine h6.bindingsSupported)
      (programText_slice (programLoaded_codeIn h6.loaded) 0x9a93 _
        (by decide) (by decide +kernel))
      ⟨e6.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t6 (t6.regValue .rbx + 16#64) 8
        rw [h6.output]
        exact (output_writable pre h6.toFrame).add 16 (by decide), by
        change RangeApart (t6.regValue .rbx + 16#64) 8 0x109a93 4
        rw [h6.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a93) (len := 4) (by decide)) 16 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a97 (by decide)))
  change (movM64R64Effect 0x109a93 6 (.base 3 (.d8 16)) t6).Holds t6 t7 at e7
  have f7 : AgreesExcept [.mem (s.regValue .rdi + 16#64) 8, .rip] t6 t7 := by
    have address (v : RamState) : storeAddrAt 0x109a93 (.base 3 (.d8 16)) 4 v = v.regValue .rbx + 16#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a93 (.base 3 (.d8 16)) 4 t6) 8, .rip] t6 t7 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e7.agrees
    simpa only [address, h6.output] using hf
  have h7 := after_output_store pre h6 a7 r7 f7 (by decide)
  have payload7 := payload6.of_agrees f7 (by simp)
  have v7 : memLoad t7.external (s.regValue .rdi + 16#64) 64 = BitVec.ofNat 64 (x / 2^64) := by
    have hw : memLoad t7.external (t6.regValue .rbx + 16#64) 64 =
        (Operand.reg 6 : Operand 64).read t6 := e7.writes
    rw [h6.output] at hw
    exact hw.trans payload6.rsi
  obtain ⟨t8, a8, r8, e8⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109a97 0x48
      (by simp [RexWPrefix]) 2 (.base 3 (.d8 8)) (by decide) rfl rfl).advances
      (readyToStep h7.machine h7.bindingsSupported)
      (programText_slice (programLoaded_codeIn h7.loaded) 0x9a97 _
        (by decide) (by decide +kernel))
      ⟨e7.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t7 (t7.regValue .rbx + 8#64) 8
        rw [h7.output]
        exact (output_writable pre h7.toFrame).add 8 (by decide), by
        change RangeApart (t7.regValue .rbx + 8#64) 8 0x109a97 4
        rw [h7.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9a97) (len := 4) (by decide)) 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a9b (by decide)))
  change (movM64R64Effect 0x109a97 2 (.base 3 (.d8 8)) t7).Holds t7 t8 at e8
  have f8 : AgreesExcept [.mem (s.regValue .rdi + 8#64) 8, .rip] t7 t8 := by
    have address (v : RamState) : storeAddrAt 0x109a97 (.base 3 (.d8 8)) 4 v = v.regValue .rbx + 8#64 := rfl
    have hf : AgreesExcept [.mem (storeAddrAt 0x109a97 (.base 3 (.d8 8)) 4 t7) 8, .rip] t7 t8 := by
      simpa only [movM64R64Effect, storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd] using e8.agrees
    simpa only [address, h7.output] using hf
  have h8 := after_output_store pre h7 a8 r8 f8 (by decide)
  have payload8 := payload7.of_agrees f8 (by simp)
  have v8 : memLoad t8.external (s.regValue .rdi + 8#64) 64 = BitVec.ofNat 64 (x / 2^0) := by
    have hw : memLoad t8.external (t7.regValue .rbx + 8#64) 64 =
        (Operand.reg 2 : Operand 64).read t7 := e8.writes
    rw [h7.output] at hw
    exact hw.trans payload7.rdx
  refine ⟨t8, h8, e8.rip, ?_, ?_⟩
  · apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs first.1
    · exact ((output_writable pre h8.toFrame).add 8 (len := 32) (by decide)).mem
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · change memLoad t8.external (s.regValue .rdi + 8#64 + 0#64) 64 = BitVec.ofNat 64 (x / 2^0)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using v8
      · change memLoad t8.external (s.regValue .rdi + 8#64 + 8#64) 64 = BitVec.ofNat 64 (x / 2^64)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 16) (by unfold OffsetsApart; decide +kernel)).trans (v7)
      · change memLoad t8.external (s.regValue .rdi + 8#64 + 16#64) 64 = BitVec.ofNat 64 (x / 2^128)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 24) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 24) (by unfold OffsetsApart; decide +kernel)).trans (v6))
      · change memLoad t8.external (s.regValue .rdi + 8#64 + 24#64) 64 = BitVec.ofNat 64 (x / 2^192)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 32) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 32) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f6 (target := 32) (by unfold OffsetsApart; decide +kernel)).trans (v5)))
  · apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs second.1
    · exact ((output_writable pre h8.toFrame).add 40 (len := 32) (by decide)).mem
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · change memLoad t8.external (s.regValue .rdi + 40#64 + 0#64) 64 = BitVec.ofNat 64 (y / 2^0)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 40) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 40) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f6 (target := 40) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f5 (target := 40) (by unfold OffsetsApart; decide +kernel)).trans (v4))))
      · change memLoad t8.external (s.regValue .rdi + 40#64 + 8#64) 64 = BitVec.ofNat 64 (y / 2^64)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 48) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 48) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f6 (target := 48) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f5 (target := 48) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f4 (target := 48) (by unfold OffsetsApart; decide +kernel)).trans (v3)))))
      · change memLoad t8.external (s.regValue .rdi + 40#64 + 16#64) 64 = BitVec.ofNat 64 (y / 2^128)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f6 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f5 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f4 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f3 (target := 56) (by unfold OffsetsApart; decide +kernel)).trans (v2))))))
      · change memLoad t8.external (s.regValue .rdi + 40#64 + 24#64) 64 = BitVec.ofNat 64 (y / 2^192)
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (output_word_preserved f8 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f7 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f6 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f5 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f4 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f3 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans ((output_word_preserved f2 (target := 64) (by unfold OffsetsApart; decide +kernel)).trans (v1)))))))

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
