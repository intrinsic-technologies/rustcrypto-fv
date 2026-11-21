import P256.Proofs.Nonce.Fill.Entry.Prepare
import P256.Proofs.Nonce.Fill.Entry.Setup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Configured [Bindings] (initial s : RamState) (order : BitVec 64) (state : State) : Prop extends
    Frame initial s, Slots initial s where
  rip : s.RIP = 0x107387
  rdi : s.regValue .rdi = initial.regValue .rdi + 8
  r13 : s.regValue .r13 = 32
  generator : GeneratorAt s (initial.regValue .rdi) order state

theorem configure [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {order : BitVec 64} {state : State} (pre : Pre initial boundary order state)
    (input : Prepared initial s order state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Configured initial t order state := by
  have pp : SetupPre s := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro off ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl
      all_goals exact stack_writable8 pre input.toFrame (by decide) (by decide)
    · intro off ho co cl hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl
      all_goals exact stack_code pre input.toFrame (by decide) hc
  obtain ⟨fuel, t, run, ready, _, effect⟩ := setup_block boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x735a setupBytes
      (by decide) (by decide +kernel)) pp
  have shape : ∀ c ∈ (setupEffect s).components, ∀ a, c.Covers a →
      ∃ off len : Nat, off + len ≤ 184 ∧ (Component.mem (stackPtr s + BitVec.ofNat 64 off) len).Covers a := by
    intro c hc a ha
    simp only [Effect.components, setupEffect, BitVec.ofNat_eq_ofNat, Nat.reduceLeDiff, BitVec.setWidth_shiftLeft_of_le,
      List.map_cons, Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨56, 4, by decide, ha⟩
    · exact ⟨144, 8, by decide, ha⟩
    · exact ⟨136, 8, by decide, ha⟩
    · exact ⟨64, 8, by decide, ha⟩
    · exact ⟨48, 8, by decide, ha⟩
  have writes : WritesWithin (setupEffect s).components (workRegions initial) := by
    intro c hc a ha
    obtain ⟨off, len, bound, covered⟩ := shape c hc a ha
    exact ⟨_, by simp [workRegions], stack_component pre input.toFrame bound covered⟩
  have frame := input.toFrame.after_effect pre ready effect.agrees writes (by component_not_mem)
  have memory := stack_frame pre input.toFrame effect.agrees shape
  have output : memLoad t.external (stackPtr s + 40) 64 = memLoad s.external (stackPtr s + 40) 64 := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    apply effect.agrees.memory
    intro c hc ha
    simp only [Effect.components, setupEffect, BitVec.ofNat_eq_ofNat, Nat.reduceLeDiff, BitVec.setWidth_shiftLeft_of_le,
      List.map_cons, Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j, hj, eq⟩ := ha
    · exact (show OffsetsApart 56 4 40 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide) eq.symm
    · exact (show OffsetsApart 144 8 40 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide) eq.symm
    · exact (show OffsetsApart 136 8 40 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide) eq.symm
    · exact (show OffsetsApart 64 8 40 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide) eq.symm
    · exact (show OffsetsApart 48 8 40 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide) eq.symm
  have vals : t.regValue .rax = s.regValue .rdi + 40 ∧
      memLoad t.external (stackPtr s + 56) 32 = (s.regValue .r13 <<< (3 : Nat)).setWidth 32 ∧
      memLoad t.external (stackPtr s + 144) 64 = s.regValue .rdi ∧
      memLoad t.external (stackPtr s + 136) 64 = s.regValue .rdi + 40 ∧
      t.regValue .rdi = s.regValue .rcx ∧
      memLoad t.external (stackPtr s + 64) 64 = s.regValue .rcx ∧
      memLoad t.external (stackPtr s + 48) 64 = s.regValue .r13 := effect.writes
  rw [input.rsp, input.r13, input.rdi, input.rcx] at vals
  refine ⟨fuel, t, run, frame, ?_, effect.rip, vals.2.2.2.2.1, ?_, ?_⟩
  · refine ⟨?_, vals.2.2.2.2.2.2, ?_, vals.2.2.2.2.2.1, vals.2.2.2.1, vals.2.2.1⟩
    · rw [input.rsp] at output
      exact output.trans input.outputSlot
    · exact vals.2.1
  · exact (effect.agrees.read (n := 64) (r := 13) (by component_not_mem)).trans input.r13
  · exact input.generator.of_frame pre.outputBounded pre.orderBounded memory
      (by intro r hr; have h : r = Stack.region initial 2096 := by simpa using hr
          subst r; exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide))
      (by intro r hr; have h : r = Stack.region initial 2096 := by simpa using hr
          subst r; exact pre.orderDisjoint _ (by simp))

end P256.Proofs.Nonce.Fill.Entry
