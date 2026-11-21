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

theorem copy_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (rip : t.RIP = 0x10b18d)
    (rcx : t.regValue .rcx = point) (input : Nat256At s (point + 96) n) :
    ∃ fuel u, Advances boundary fuel t u ∧ Memory s u cursor point ∧
      u.RIP = 0x10b1ca ∧ u.regValue .rdi = stackPtr t + 8 ∧
      u.regValue .rsi = stackPtr t + 280 ∧ u.regValue .rbx = t.regValue .rbx ∧
      Nat256At u (stackPtr t + 280) n := by
  have pointer1 : t.regValue .rcx = point := rcx
  obtain ⟨t1, run1, ready1, e1⟩ := (mov_r64_m64_effect_step 0x10b18d 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 120)) (by decide +kernel) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb18d
      [0x48, 0x8b, 0x41, 0x78] (by decide) (by decide +kernel))
    ⟨rip, by
        change MemReadable t (t.regValue .rcx + 120#64) 8
        rw [pointer1]
        exact scalar_readable pre state.toFrameState (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb191 (by decide)))
  change (movR64M64Effect 0x10b18d 0 (.base 1 (.d8 120)) t).Holds t t1 at e1
  have a1 : AgreesExcept [.reg 0, .rip] t t1 := e1.agrees
  have memory1 : t1.external = t.external := a1.external (by simp [Component.Covers])
  have state1 := state.registers ready1 a1 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb1 : t1.regValue .rax = BitVec.ofNat 64 (n / 2^(64*3)) := by
    have h := (input_at pre state.toFrameState input).memLoad_limb 3 (by decide)
    have he := e1.writes
    change t1.regValue .rax = memLoad t.external (t.regValue .rcx + 120#64) 64 at he
    rw [pointer1] at he
    have h' : memLoad t.external (point + 120#64) 64 = BitVec.ofNat 64 (n / 2^(64*3)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag1 := a1
  obtain ⟨t2, run2, ready2, e2⟩ := (mov_m64_r64_effect_step_any 0x10b191 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl).advances
    (readyToStep state1.machine state1.bindingsSupported)
    (programText_slice (programLoaded_codeIn state1.loaded) 0xb191
      [0x48, 0x89, 0x84, 0x24, 0x30, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e1.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1 (stackPtr t1 + 304#64) 8
        exact stack_writable pre state1.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t1 + 304#64) 8 0x10b191 8
        exact stack_code pre state1.toFrameState (offset := 304) (len := 8) (codeOffset := 0xb191) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb199 (by decide)))
  change ({ rip := 0x10b199, writes := [⟨(Operand.mem (stackPtr t1 + 304#64) : Operand 64), t1.regValue .rax⟩] } : Effect).Holds t1 t2 at e2
  have a2 : AgreesExcept [.mem (stackPtr t1 + 304#64) 8, .rip] t1 t2 := by
    simpa [Effect.components] using e2.agrees
  have state2 := state1.after_store pre ready2 (by decide) a2
  have sp2 : stackPtr t1 = stackPtr t := ag1.read (n := 64) (r := 4) (by simp)
  have slot2 : AgreesExcept [.mem (stackPtr t + 304#64) 8, .rip] t1 t2 := by
    simpa only [sp2] using a2
  have value2 : memLoad t2.external (stackPtr t + 304#64) 64 = BitVec.ofNat 64 (n / 2^(64*3)) := by
    have h := e2.writes
    change memLoad t2.external (stackPtr t1 + 304#64) 64 = t1.regValue .rax at h
    rw [sp2] at h
    exact h.trans limb1
  have ag2 := ag1.trans a2
  have pointer3 : t2.regValue .rcx = point := (ag2.read (n := 64) (r := 1) (by simp)).trans rcx
  obtain ⟨t3, run3, ready3, e3⟩ := (mov_r64_m64_effect_step 0x10b199 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 112)) (by decide +kernel) rfl rfl).advances
    (readyToStep state2.machine state2.bindingsSupported)
    (programText_slice (programLoaded_codeIn state2.loaded) 0xb199
      [0x48, 0x8b, 0x41, 0x70] (by decide) (by decide +kernel))
    ⟨e2.rip, by
        change MemReadable t2 (t2.regValue .rcx + 112#64) 8
        rw [pointer3]
        exact scalar_readable pre state2.toFrameState (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb19d (by decide)))
  change (movR64M64Effect 0x10b199 0 (.base 1 (.d8 112)) t2).Holds t2 t3 at e3
  have a3 : AgreesExcept [.reg 0, .rip] t2 t3 := e3.agrees
  have memory3 : t3.external = t2.external := a3.external (by simp [Component.Covers])
  have state3 := state2.registers ready3 a3 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb3 : t3.regValue .rax = BitVec.ofNat 64 (n / 2^(64*2)) := by
    have h := (input_at pre state2.toFrameState input).memLoad_limb 2 (by decide)
    have he := e3.writes
    change t3.regValue .rax = memLoad t2.external (t2.regValue .rcx + 112#64) 64 at he
    rw [pointer3] at he
    have h' : memLoad t2.external (point + 112#64) 64 = BitVec.ofNat 64 (n / 2^(64*2)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag3 := ag2.trans a3
  obtain ⟨t4, run4, ready4, e4⟩ := (mov_m64_r64_effect_step_any 0x10b19d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl).advances
    (readyToStep state3.machine state3.bindingsSupported)
    (programText_slice (programLoaded_codeIn state3.loaded) 0xb19d
      [0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e3.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t3 (stackPtr t3 + 296#64) 8
        exact stack_writable pre state3.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t3 + 296#64) 8 0x10b19d 8
        exact stack_code pre state3.toFrameState (offset := 296) (len := 8) (codeOffset := 0xb19d) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1a5 (by decide)))
  change ({ rip := 0x10b1a5, writes := [⟨(Operand.mem (stackPtr t3 + 296#64) : Operand 64), t3.regValue .rax⟩] } : Effect).Holds t3 t4 at e4
  have a4 : AgreesExcept [.mem (stackPtr t3 + 296#64) 8, .rip] t3 t4 := by
    simpa [Effect.components] using e4.agrees
  have state4 := state3.after_store pre ready4 (by decide) a4
  have sp4 : stackPtr t3 = stackPtr t := ag3.read (n := 64) (r := 4) (by simp)
  have slot4 : AgreesExcept [.mem (stackPtr t + 296#64) 8, .rip] t3 t4 := by
    simpa only [sp4] using a4
  have value4 : memLoad t4.external (stackPtr t + 296#64) 64 = BitVec.ofNat 64 (n / 2^(64*2)) := by
    have h := e4.writes
    change memLoad t4.external (stackPtr t3 + 296#64) 64 = t3.regValue .rax at h
    rw [sp4] at h
    exact h.trans limb3
  have ag4 := ag3.trans a4
  have pointer5 : t4.regValue .rcx = point := (ag4.read (n := 64) (r := 1) (by simp)).trans rcx
  obtain ⟨t5, run5, ready5, e5⟩ := (mov_r64_m64_effect_step 0x10b1a5 0x48 (by simp [RexWPrefix]) 0 (.base 1 (.d8 96)) (by decide +kernel) rfl rfl).advances
    (readyToStep state4.machine state4.bindingsSupported)
    (programText_slice (programLoaded_codeIn state4.loaded) 0xb1a5
      [0x48, 0x8b, 0x41, 0x60] (by decide) (by decide +kernel))
    ⟨e4.rip, by
        change MemReadable t4 (t4.regValue .rcx + 96#64) 8
        rw [pointer5]
        exact scalar_readable pre state4.toFrameState (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1a9 (by decide)))
  change (movR64M64Effect 0x10b1a5 0 (.base 1 (.d8 96)) t4).Holds t4 t5 at e5
  have a5 : AgreesExcept [.reg 0, .rip] t4 t5 := e5.agrees
  have memory5 : t5.external = t4.external := a5.external (by simp [Component.Covers])
  have state5 := state4.registers ready5 a5 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb5 : t5.regValue .rax = BitVec.ofNat 64 (n / 2^(64*0)) := by
    have h := (input_at pre state4.toFrameState input).memLoad_limb 0 (by decide)
    have he := e5.writes
    change t5.regValue .rax = memLoad t4.external (t4.regValue .rcx + 96#64) 64 at he
    rw [pointer5] at he
    have h' : memLoad t4.external (point + 96#64) 64 = BitVec.ofNat 64 (n / 2^(64*0)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag5 := ag4.trans a5
  have pointer6 : t5.regValue .rcx = point := (ag5.read (n := 64) (r := 1) (by simp)).trans rcx
  obtain ⟨t6, run6, ready6, e6⟩ := (mov_r64_m64_effect_step 0x10b1a9 0x48 (by simp [RexWPrefix]) 1 (.base 1 (.d8 104)) (by decide +kernel) rfl rfl).advances
    (readyToStep state5.machine state5.bindingsSupported)
    (programText_slice (programLoaded_codeIn state5.loaded) 0xb1a9
      [0x48, 0x8b, 0x49, 0x68] (by decide) (by decide +kernel))
    ⟨e5.rip, by
        change MemReadable t5 (t5.regValue .rcx + 104#64) 8
        rw [pointer6]
        exact scalar_readable pre state5.toFrameState (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1ad (by decide)))
  change (movR64M64Effect 0x10b1a9 1 (.base 1 (.d8 104)) t5).Holds t5 t6 at e6
  have a6 : AgreesExcept [.reg 1, .rip] t5 t6 := e6.agrees
  have memory6 : t6.external = t5.external := a6.external (by simp [Component.Covers])
  have state6 := state5.registers ready6 a6 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have limb6 : t6.regValue .rcx = BitVec.ofNat 64 (n / 2^(64*1)) := by
    have h := (input_at pre state5.toFrameState input).memLoad_limb 1 (by decide)
    have he := e6.writes
    change t6.regValue .rcx = memLoad t5.external (t5.regValue .rcx + 104#64) 64 at he
    rw [pointer6] at he
    have h' : memLoad t5.external (point + 104#64) 64 = BitVec.ofNat 64 (n / 2^(64*1)) := by
      simpa only [Nat.mul_zero, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul] using h
    exact he.trans h'
  have ag6 := ag5.trans a6
  obtain ⟨t7, run7, ready7, e7⟩ := (mov_m64_r64_effect_step_any 0x10b1ad 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl).advances
    (readyToStep state6.machine state6.bindingsSupported)
    (programText_slice (programLoaded_codeIn state6.loaded) 0xb1ad
      [0x48, 0x89, 0x8c, 0x24, 0x20, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e6.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t6 (stackPtr t6 + 288#64) 8
        exact stack_writable pre state6.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t6 + 288#64) 8 0x10b1ad 8
        exact stack_code pre state6.toFrameState (offset := 288) (len := 8) (codeOffset := 0xb1ad) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1b5 (by decide)))
  change ({ rip := 0x10b1b5, writes := [⟨(Operand.mem (stackPtr t6 + 288#64) : Operand 64), t6.regValue .rcx⟩] } : Effect).Holds t6 t7 at e7
  have a7 : AgreesExcept [.mem (stackPtr t6 + 288#64) 8, .rip] t6 t7 := by
    simpa [Effect.components] using e7.agrees
  have state7 := state6.after_store pre ready7 (by decide) a7
  have sp7 : stackPtr t6 = stackPtr t := ag6.read (n := 64) (r := 4) (by simp)
  have slot7 : AgreesExcept [.mem (stackPtr t + 288#64) 8, .rip] t6 t7 := by
    simpa only [sp7] using a7
  have value7 : memLoad t7.external (stackPtr t + 288#64) 64 = BitVec.ofNat 64 (n / 2^(64*1)) := by
    have h := e7.writes
    change memLoad t7.external (stackPtr t6 + 288#64) 64 = t6.regValue .rcx at h
    rw [sp7] at h
    exact h.trans limb6
  have ag7 := ag6.trans a7
  obtain ⟨t8, run8, ready8, e8⟩ := (mov_m64_r64_effect_step_any 0x10b1b5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl).advances
    (readyToStep state7.machine state7.bindingsSupported)
    (programText_slice (programLoaded_codeIn state7.loaded) 0xb1b5
      [0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    ⟨e7.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t7 (stackPtr t7 + 280#64) 8
        exact stack_writable pre state7.toFrameState (by decide) (by decide)
      , by
        change RangeApart (stackPtr t7 + 280#64) 8 0x10b1b5 8
        exact stack_code pre state7.toFrameState (offset := 280) (len := 8) (codeOffset := 0xb1b5) (codeLen := 8) (by decide) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1bd (by decide)))
  change ({ rip := 0x10b1bd, writes := [⟨(Operand.mem (stackPtr t7 + 280#64) : Operand 64), t7.regValue .rax⟩] } : Effect).Holds t7 t8 at e8
  have a8 : AgreesExcept [.mem (stackPtr t7 + 280#64) 8, .rip] t7 t8 := by
    simpa [Effect.components] using e8.agrees
  have state8 := state7.after_store pre ready8 (by decide) a8
  have sp8 : stackPtr t7 = stackPtr t := ag7.read (n := 64) (r := 4) (by simp)
  have slot8 : AgreesExcept [.mem (stackPtr t + 280#64) 8, .rip] t7 t8 := by
    simpa only [sp8] using a8
  have value8 : memLoad t8.external (stackPtr t + 280#64) 64 = BitVec.ofNat 64 (n / 2^(64*0)) := by
    have h := e8.writes
    change memLoad t8.external (stackPtr t7 + 280#64) 64 = t7.regValue .rax at h
    rw [sp8] at h
    exact h.trans (((a7.read (n := 64) (r := 0) (by simp)).trans
      (a6.read (n := 64) (r := 0) (by simp))).trans limb5)
  have ag8 := ag7.trans a8
  obtain ⟨t9, run9, ready9, e9⟩ := (lea_r64_effect_step 0x10b1bd 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
    (readyToStep state8.machine state8.bindingsSupported)
    (programText_slice (programLoaded_codeIn state8.loaded) 0xb1bd
      [0x48, 0x8d, 0x7c, 0x24, 0x8] (by decide) (by decide +kernel))
    e8.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1c2 (by decide)))
  change (leaR64Effect 0x10b1bd 7 (.sib 4 none 0 (.d8 8)) t8).Holds t8 t9 at e9
  have a9 : AgreesExcept [.reg 7, .rip] t8 t9 := e9.agrees
  have memory9 : t9.external = t8.external := a9.external (by simp [Component.Covers])
  have state9 := state8.registers ready9 a9 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have ag9 := ag8.trans a9
  obtain ⟨t10, run10, ready10, e10⟩ := (lea_r64_effect_step 0x10b1c2 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl).advances
    (readyToStep state9.machine state9.bindingsSupported)
    (programText_slice (programLoaded_codeIn state9.loaded) 0xb1c2
      [0x48, 0x8d, 0xb4, 0x24, 0x18, 0x1, 0x0, 0x0] (by decide) (by decide +kernel))
    e9.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb1ca (by decide)))
  change (leaR64Effect 0x10b1c2 6 (.sib 4 none 0 (.d32 280)) t9).Holds t9 t10 at e10
  have a10 : AgreesExcept [.reg 6, .rip] t9 t10 := e10.agrees
  have memory10 : t10.external = t9.external := a10.external (by simp [Component.Covers])
  have state10 := state9.registers ready10 a10 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have ag10 := ag9.trans a10
  refine ⟨10, t10, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans
    (run6.trans (run7.trans (run8.trans (run9.trans run10)))))))), state10, e10.rip, ?_, ?_,
    ag10.read (n := 64) (r := 3) (by simp), ?_⟩
  · exact (a10.read (n := 64) (r := 7) (by simp)).trans
      (e9.writes.trans (congrArg (· + 8) (ag8.read (n := 64) (r := 4) (by simp))))
  · exact e10.writes.trans (congrArg (· + 280) (ag9.read (n := 64) (r := 4) (by simp)))
  · apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (address := stackPtr t + 280#64) input.1
    · intro i hi
      have h := stack_readable pre state10.toFrameState (offset := 280) (len := 32) (by decide)
      have sp10 : stackPtr t10 = stackPtr t := ag10.read (n := 64) (r := 4) (by simp)
      rw [sp10] at h
      exact h.mem i hi
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rw [memory10, memory9]
      rcases cases with rfl | rfl | rfl | rfl
      all_goals simp only [Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
      · exact value8
      · change memLoad t8.external (stackPtr t + 288#64) 64 = _
        rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel)]
        exact value7
      · change memLoad t8.external (stackPtr t + 296#64) 64 = _
        rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel),
          Iterator.slot_read slot7 (by unfold OffsetsApart; decide +kernel), memory6, memory5]
        exact value4
      · change memLoad t8.external (stackPtr t + 304#64) 64 = _
        rw [Iterator.slot_read slot8 (by unfold OffsetsApart; decide +kernel),
          Iterator.slot_read slot7 (by unfold OffsetsApart; decide +kernel), memory6, memory5,
          Iterator.slot_read slot4 (by unfold OffsetsApart; decide +kernel), memory3]
        exact value2

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
