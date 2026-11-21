import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Encode.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field
open P256.Proofs.Common.Instructions.CrossPageStore

theorem nat256_store {s t : RamState} {base written source : BitVec 64} {n : Nat}
    (agrees : AgreesExcept [.mem (base + written) 8, .rip] s t)
    (apart : OffsetsApart written 8 source 32) (input : Nat256At s (base + source) n) :
    Nat256At t (base + source) n := by
  refine ⟨input.1, ?_⟩
  intro i hi
  apply Eq.trans (agrees.byte ?_) (input.2 i hi)
  intro c hc ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := ha
    exact apart.ne base hj hi (by decide) he.symm
  · exact ha.elim

theorem copy_reversed_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (rip : t.RIP = 0x10b2d7)
    (input : Nat256At t (stackPtr t + 8) n) :
    ∃ fuel u, Advances boundary fuel t u ∧ Memory s u cursor point ∧
      u.RIP = 0x10b30b ∧ u.regValue .rbx = t.regValue .rbx ∧
      Nat256At u (stackPtr s - 48) n := by
  have pointer1 : stackPtr t = stackPtr t := rfl
  obtain ⟨t1, run1, ready1, e1⟩ := (mov_r64_m64_effect_step 0x10b2d7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb2d7
      [0x48, 0x8b, 0x44, 0x24, 0x10] (by decide) (by decide +kernel))
    ⟨rip, by
        change MemReadable t (stackPtr t + 16#64) 8
        exact stack_readable pre state.toFrameState (offset := 16) (len := 8) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2dc (by decide)))
  change (movR64M64Effect 0x10b2d7 0 (.sib 4 none 0 (.d8 16)) t).Holds t t1 at e1
  have a1 : AgreesExcept [.reg 0, .rip] t t1 := e1.agrees
  have memory1 : t1.external = t.external := a1.external (by simp [Component.Covers])
  have state1 := state.registers ready1 a1 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb1 : t1.regValue .rax = BitVec.ofNat 64 (n / 2^(64*1)) := by
    have h := input.memLoad_limb 1 (by decide)
    have he := e1.writes
    change t1.regValue .rax = memLoad t.external (stackPtr t + 16#64) 64 at he
    rw [pointer1] at he
    have h' : memLoad t.external (stackPtr t + 16#64) 64 = BitVec.ofNat 64 (n / 2^(64*1)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag1 := a1
  have input1 : Nat256At t1 (stackPtr t + 8) n := by
    exact ⟨input.1, fun i hi => by rw [memory1]; exact input.2 i hi⟩
  obtain ⟨t2, run2, ready2, e2⟩ := (mov_m64_r64_effect_step_any 0x10b2dc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl).advances
    (readyToStep state1.machine state1.bindingsSupported)
    (programText_slice (programLoaded_codeIn state1.loaded) 0xb2dc
      [0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e1.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1 (stackPtr t1 + 320#64) 8
        exact stack_writable pre state1.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t1 + 320#64) 8 0x10b2dc 8
        exact stack_code pre state1.toFrameState (offset := 320) (len := 8) (codeOffset := 0xb2dc) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2e4 (by decide)))
  change ({ rip := 0x10b2e4, writes := [⟨(Operand.mem (stackPtr t1 + 320#64) : Operand 64), t1.regValue .rax⟩] } : Effect).Holds t1 t2 at e2
  have a2 : AgreesExcept [.mem (stackPtr t1 + 320#64) 8, .rip] t1 t2 := by
    simpa [Effect.components] using e2.agrees
  have state2 := state1.after_store pre ready2 (by decide) a2
  have sp2 : stackPtr t1 = stackPtr t := ag1.read (n := 64) (r := 4) (by simp)
  have slot2 : AgreesExcept [.mem (stackPtr t + 320#64) 8, .rip] t1 t2 := by
    simpa only [sp2] using a2
  have value2 : memLoad t2.external (stackPtr t + 320#64) 64 = BitVec.ofNat 64 (n / 2^(64*1)) := by
    have h := e2.writes
    change memLoad t2.external (stackPtr t1 + 320#64) 64 = t1.regValue .rax at h
    rw [sp2] at h
    exact h.trans limb1
  have ag2 := ag1.trans a2
  have input2 := nat256_store slot2 (by unfold OffsetsApart; decide +kernel) input1
  have pointer3 : stackPtr t2 = stackPtr t := ag2.read (n := 64) (r := 4) (by simp)
  obtain ⟨t3, run3, ready3, e3⟩ := (mov_r64_m64_effect_step 0x10b2e4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl).advances
    (readyToStep state2.machine state2.bindingsSupported)
    (programText_slice (programLoaded_codeIn state2.loaded) 0xb2e4
      [0x48, 0x8b, 0x44, 0x24, 0x20] (by decide) (by decide +kernel))
    ⟨e2.rip, by
        change MemReadable t2 (stackPtr t2 + 32#64) 8
        exact stack_readable pre state2.toFrameState (offset := 32) (len := 8) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2e9 (by decide)))
  change (movR64M64Effect 0x10b2e4 0 (.sib 4 none 0 (.d8 32)) t2).Holds t2 t3 at e3
  have a3 : AgreesExcept [.reg 0, .rip] t2 t3 := e3.agrees
  have memory3 : t3.external = t2.external := a3.external (by simp [Component.Covers])
  have state3 := state2.registers ready3 a3 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb3 : t3.regValue .rax = BitVec.ofNat 64 (n / 2^(64*3)) := by
    have h := input2.memLoad_limb 3 (by decide)
    have he := e3.writes
    change t3.regValue .rax = memLoad t2.external (stackPtr t2 + 32#64) 64 at he
    rw [pointer3] at he
    have h' : memLoad t2.external (stackPtr t + 32#64) 64 = BitVec.ofNat 64 (n / 2^(64*3)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag3 := ag2.trans a3
  have input3 : Nat256At t3 (stackPtr t + 8) n := by
    exact ⟨input2.1, fun i hi => by rw [memory3]; exact input2.2 i hi⟩
  obtain ⟨t4, run4, ready4, e4⟩ := (mov_m64_r64_effect_step_any 0x10b2e9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl).advances
    (readyToStep state3.machine state3.bindingsSupported)
    (programText_slice (programLoaded_codeIn state3.loaded) 0xb2e9
      [0x48, 0x89, 0x84, 0x24, 0x50, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e3.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t3 (stackPtr t3 + 336#64) 8
        exact stack_writable pre state3.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t3 + 336#64) 8 0x10b2e9 8
        exact stack_code pre state3.toFrameState (offset := 336) (len := 8) (codeOffset := 0xb2e9) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2f1 (by decide)))
  change ({ rip := 0x10b2f1, writes := [⟨(Operand.mem (stackPtr t3 + 336#64) : Operand 64), t3.regValue .rax⟩] } : Effect).Holds t3 t4 at e4
  have a4 : AgreesExcept [.mem (stackPtr t3 + 336#64) 8, .rip] t3 t4 := by
    simpa [Effect.components] using e4.agrees
  have state4 := state3.after_store pre ready4 (by decide) a4
  have sp4 : stackPtr t3 = stackPtr t := ag3.read (n := 64) (r := 4) (by simp)
  have slot4 : AgreesExcept [.mem (stackPtr t + 336#64) 8, .rip] t3 t4 := by
    simpa only [sp4] using a4
  have value4 : memLoad t4.external (stackPtr t + 336#64) 64 = BitVec.ofNat 64 (n / 2^(64*3)) := by
    have h := e4.writes
    change memLoad t4.external (stackPtr t3 + 336#64) 64 = t3.regValue .rax at h
    rw [sp4] at h
    exact h.trans limb3
  have ag4 := ag3.trans a4
  have input4 := nat256_store slot4 (by unfold OffsetsApart; decide +kernel) input3
  have pointer5 : stackPtr t4 = stackPtr t := ag4.read (n := 64) (r := 4) (by simp)
  obtain ⟨t5, run5, ready5, e5⟩ := (mov_r64_m64_effect_step 0x10b2f1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
    (readyToStep state4.machine state4.bindingsSupported)
    (programText_slice (programLoaded_codeIn state4.loaded) 0xb2f1
      [0x48, 0x8b, 0x44, 0x24, 0x8] (by decide) (by decide +kernel))
    ⟨e4.rip, by
        change MemReadable t4 (stackPtr t4 + 8#64) 8
        exact stack_readable pre state4.toFrameState (offset := 8) (len := 8) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2f6 (by decide)))
  change (movR64M64Effect 0x10b2f1 0 (.sib 4 none 0 (.d8 8)) t4).Holds t4 t5 at e5
  have a5 : AgreesExcept [.reg 0, .rip] t4 t5 := e5.agrees
  have memory5 : t5.external = t4.external := a5.external (by simp [Component.Covers])
  have state5 := state4.registers ready5 a5 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb5 : t5.regValue .rax = BitVec.ofNat 64 (n / 2^(64*0)) := by
    have h := input4.memLoad_limb 0 (by decide)
    have he := e5.writes
    change t5.regValue .rax = memLoad t4.external (stackPtr t4 + 8#64) 64 at he
    rw [pointer5] at he
    have h' : memLoad t4.external (stackPtr t + 8#64) 64 = BitVec.ofNat 64 (n / 2^(64*0)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag5 := ag4.trans a5
  have input5 : Nat256At t5 (stackPtr t + 8) n := by
    exact ⟨input4.1, fun i hi => by rw [memory5]; exact input4.2 i hi⟩
  have pointer6 : stackPtr t5 = stackPtr t := ag5.read (n := 64) (r := 4) (by simp)
  obtain ⟨t6, run6, ready6, e6⟩ := (mov_r64_m64_effect_step 0x10b2f6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl).advances
    (readyToStep state5.machine state5.bindingsSupported)
    (programText_slice (programLoaded_codeIn state5.loaded) 0xb2f6
      [0x48, 0x8b, 0x4c, 0x24, 0x18] (by decide) (by decide +kernel))
    ⟨e5.rip, by
        change MemReadable t5 (stackPtr t5 + 24#64) 8
        exact stack_readable pre state5.toFrameState (offset := 24) (len := 8) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb2fb (by decide)))
  change (movR64M64Effect 0x10b2f6 1 (.sib 4 none 0 (.d8 24)) t5).Holds t5 t6 at e6
  have a6 : AgreesExcept [.reg 1, .rip] t5 t6 := e6.agrees
  have memory6 : t6.external = t5.external := a6.external (by simp [Component.Covers])
  have state6 := state5.registers ready6 a6 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb6 : t6.regValue .rcx = BitVec.ofNat 64 (n / 2^(64*2)) := by
    have h := input5.memLoad_limb 2 (by decide)
    have he := e6.writes
    change t6.regValue .rcx = memLoad t5.external (stackPtr t5 + 24#64) 64 at he
    rw [pointer6] at he
    have h' : memLoad t5.external (stackPtr t + 24#64) 64 = BitVec.ofNat 64 (n / 2^(64*2)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag6 := ag5.trans a6
  have input6 : Nat256At t6 (stackPtr t + 8) n := by
    exact ⟨input5.1, fun i hi => by rw [memory6]; exact input5.2 i hi⟩
  obtain ⟨t7, run7, ready7, e7⟩ := (mov_m64_r64_effect_step_any 0x10b2fb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl).advances
    (readyToStep state6.machine state6.bindingsSupported)
    (programText_slice (programLoaded_codeIn state6.loaded) 0xb2fb
      [0x48, 0x89, 0x8c, 0x24, 0x48, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e6.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t6 (stackPtr t6 + 328#64) 8
        exact stack_writable pre state6.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t6 + 328#64) 8 0x10b2fb 8
        exact stack_code pre state6.toFrameState (offset := 328) (len := 8) (codeOffset := 0xb2fb) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb303 (by decide)))
  change ({ rip := 0x10b303, writes := [⟨(Operand.mem (stackPtr t6 + 328#64) : Operand 64), t6.regValue .rcx⟩] } : Effect).Holds t6 t7 at e7
  have a7 : AgreesExcept [.mem (stackPtr t6 + 328#64) 8, .rip] t6 t7 := by
    simpa [Effect.components] using e7.agrees
  have state7 := state6.after_store pre ready7 (by decide) a7
  have sp7 : stackPtr t6 = stackPtr t := ag6.read (n := 64) (r := 4) (by simp)
  have slot7 : AgreesExcept [.mem (stackPtr t + 328#64) 8, .rip] t6 t7 := by
    simpa only [sp7] using a7
  have value7 : memLoad t7.external (stackPtr t + 328#64) 64 = BitVec.ofNat 64 (n / 2^(64*2)) := by
    have h := e7.writes
    change memLoad t7.external (stackPtr t6 + 328#64) 64 = t6.regValue .rcx at h
    rw [sp7] at h
    exact h.trans limb6
  have ag7 := ag6.trans a7
  have input7 := nat256_store slot7 (by unfold OffsetsApart; decide +kernel) input6
  obtain ⟨t8, run8, ready8, e8⟩ := (mov_m64_r64_effect_step_any 0x10b303 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl).advances
    (readyToStep state7.machine state7.bindingsSupported)
    (programText_slice (programLoaded_codeIn state7.loaded) 0xb303
      [0x48, 0x89, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e7.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t7 (stackPtr t7 + 312#64) 8
        exact stack_writable pre state7.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t7 + 312#64) 8 0x10b303 8
        exact stack_code pre state7.toFrameState (offset := 312) (len := 8) (codeOffset := 0xb303) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb30b (by decide)))
  change ({ rip := 0x10b30b, writes := [⟨(Operand.mem (stackPtr t7 + 312#64) : Operand 64), t7.regValue .rax⟩] } : Effect).Holds t7 t8 at e8
  have a8 : AgreesExcept [.mem (stackPtr t7 + 312#64) 8, .rip] t7 t8 := by
    simpa [Effect.components] using e8.agrees
  have state8 := state7.after_store pre ready8 (by decide) a8
  have sp8 : stackPtr t7 = stackPtr t := ag7.read (n := 64) (r := 4) (by simp)
  have slot8 : AgreesExcept [.mem (stackPtr t + 312#64) 8, .rip] t7 t8 := by
    simpa only [sp8] using a8
  have value8 : memLoad t8.external (stackPtr t + 312#64) 64 = BitVec.ofNat 64 (n / 2^(64*0)) := by
    have h := e8.writes
    change memLoad t8.external (stackPtr t7 + 312#64) 64 = t7.regValue .rax at h
    rw [sp8] at h
    exact h.trans (((a7.read (n := 64) (r := 0) (by simp)).trans
      (a6.read (n := 64) (r := 0) (by simp))).trans limb5)
  have ag8 := ag7.trans a8
  have input8 := nat256_store slot8 (by unfold OffsetsApart; decide +kernel) input7
  refine ⟨8, t8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans
    (run6.trans (run7.trans run8)))))), state8, e8.rip,
    ag8.read (n := 64) (r := 3) (by simp), ?_⟩
  have address : stackPtr t + 312#64 = stackPtr s - 48 :=
    stack_address state.rsp (offset := 312) (by decide)
  rw [← address]
  apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (address := stackPtr t + 312#64) input.1
  · intro i hi
    have h := stack_readable pre state8.toFrameState (offset := 312) (len := 32) (by decide)
    have sp8 : stackPtr t8 = stackPtr t := ag8.read (n := 64) (r := 4) (by simp)
    rw [sp8] at h
    exact h.mem i hi
  · intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    · exact value8
    · change memLoad t8.external (stackPtr t + 320#64) 64 = _
      rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel),
        Iterator.slot_read slot7 (by unfold OffsetsApart; decide +kernel), memory6, memory5,
        Iterator.slot_read slot4 (by unfold OffsetsApart; decide +kernel), memory3]
      exact value2
    · change memLoad t8.external (stackPtr t + 328#64) 64 = _
      rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel)]
      exact value7
    · change memLoad t8.external (stackPtr t + 336#64) 64 = _
      rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel),
        Iterator.slot_read slot7 (by unfold OffsetsApart; decide +kernel), memory6, memory5]
      exact value4

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
