import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Frame
import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Setup
import P256.Proofs.Projective.Multiply.Machine.Lookup.Copy
import P256.Proofs.Projective.Multiply.Machine.Lookup.Constants
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InitializedState [Bindings] (s t : RamState) : Prop extends FrameState s t where
  rip : t.RIP = 0x1044d3
  value : ProjectiveAt t (stackPtr s - 344) Projective.identity
  r13 : t.regValue .r13 = s.regValue .rsi
  rbp : t.regValue .rbp = stackPtr s - 344
  rdx : t.regValue .rdx = s.regValue .rdx
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi

set_option maxHeartbeats 800000 in
theorem initialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) :
    ∃ fuel t, Advances boundary fuel s t ∧ InitializedState s t := by
  obtain ⟨u, run, state, rip, _, frame⟩ := frame_entry pre
  have rsi : u.regValue .rsi = s.regValue .rsi :=
    frame.read (n := 64) (r := 6) (by simp [P256.Proofs.Program.saveFrame])
  have rdi : u.regValue .rdi = s.regValue .rdi :=
    frame.read (n := 64) (r := 7) (by simp [P256.Proofs.Program.saveFrame])
  have rdx : u.regValue .rdx = s.regValue .rdx :=
    frame.read (n := 64) (r := 2) (by simp [P256.Proofs.Program.saveFrame])
  obtain ⟨n, v, run', ready, _, effect⟩ := setup_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x44b1 setupBytes
      (by decide) (by decide +kernel))
    ⟨rip, stack_writable pre state (offset := 208) (by decide) (by decide),
      stack_code pre state (offset := 208) (len := 8) (codeOffset := 0x44b1)
        (by decide) (by decide)⟩
  have address : stackPtr u + 208 = stackPtr s - 152 := stack_address state.rsp (by decide)
  have acc : stackPtr u + 16 = stackPtr s - 344 := stack_address state.rsp (by decide)
  have agr : AgreesExcept [.reg 13, .mem (stackPtr s - 152) 8, .reg 5,
      .reg 1, .reg 7, .reg 6, .rip] u v := by
    have h := effect.agrees
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    exact (congrArg (fun a : BitVec 64 =>
      AgreesExcept [.reg 13, .mem a 8, .reg 5, .reg 1, .reg 7, .reg 6, .rip] u v) address).mp h
  have writes : WritesWithin [.reg 13, .mem (stackPtr s - 152) 8, .reg 5,
      .reg 1, .reg 7, .reg 6, .rip] #v[registerRegion s .rdi 96, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s, by simp, work_contains pre (by decide) (by decide) ha⟩
  have state' := after pre state ready agr writes (by simp)
  have hw := effect.writes
  change v.regValue .r13 = u.regValue .rsi ∧
    (Operand.mem (stackPtr u + 208) : Operand 64).read v = u.regValue .rdi ∧
    v.regValue .rbp = stackPtr u + 16 ∧ v.regValue .rcx = 12 ∧
    v.regValue .rdi = stackPtr u + 16 ∧ v.regValue .rsi = 0x202490 at hw
  have value : ProjectiveAt v (v.regValue .rsi) Projective.identity :=
    hw.2.2.2.2.2 ▸ identity_at state'.loaded
  have source : MemReadable v (v.regValue .rsi) 96 := by
    rw [hw.2.2.2.2.2]
    exact identity_readable state'.loaded
  have disjoint : (v.regValue .rsi).toNat + 96 ≤ (v.regValue .rdi).toNat ∨
      (v.regValue .rdi).toNat + 96 ≤ (v.regValue .rsi).toNat := by
    rw [hw.2.2.2.2.2, hw.2.2.2.2.1, acc]
    exact identity_stack_disjoint pre
  obtain ⟨t, copied, state'', rip', point, agrees⟩ := copy_to_stack pre state'
    0x44d0 (by decide) (by decide +kernel) effect.rip 344 (by decide) (by decide)
    (hw.2.2.2.2.1.trans acc) hw.2.2.2.1 source disjoint value
  refine ⟨7 + n + 12, t, (run.trans run').trans copied, state'', rip', point, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 13) (by simp)).trans (hw.1.trans rsi)
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans (hw.2.2.1.trans acc)
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans
      ((agr.read (n := 64) (r := 2) (by simp)).trans rdx)
  · rw [P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees]
    · rw [← address]
      exact hw.2.1.trans rdi
    · intro i hi c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact id
      rintro ⟨j, hj, he⟩
      apply OffsetsApart.ne (c₁ := -344) (len₁ := 96) (c₂ := -152) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      simpa [BitVec.sub_eq_add_neg] using he.symm

end P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization
