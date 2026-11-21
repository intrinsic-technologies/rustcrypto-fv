import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Sec1.Decompress.Cubic.Copy

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fdcc) : CopyPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change MemReadable t (stackPtr t + i) 8
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_readable pre state (by decide) bound
  · intro i hi
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (stackPtr t + i) 8
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_writable pre state (by decide) bound (by decide)
  · intro i hi off len hc
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change RangeApart (stackPtr t + i) 8 _ len
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_code pre state (by decide) bound hc

def copyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s - 408) 32]

theorem copy_frame [Bindings] {s t u : RamState} (state : FrameState s t)
    (effect : (copyEffect t).Holds t u) : AgreesExcept (copyComponents s) t u := by
  apply agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [copyComponents]
    all_goals simp [Component.isMem] at hm
  · intro c hc a ha
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s - 408) 32, by simp [copyComponents], ?_⟩
      change (Component.mem (stackPtr s - 408) 32).Covers (stackPtr t + _ + BitVec.ofNat 64 i)
      rw [state.rsp]
    · exact ⟨i, by omega, by simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem copy_payload [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fdcc) (hx : MontgomeryAt t (stackPtr s - 288) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10fdfc ∧
      MontgomeryAt u (stackPtr s - 408) x ∧ AgreesExcept (copyComponents s) t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copy boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfdcc copyBytes
      (by decide +kernel) (by decide +kernel)) (copy_pre pre state rip)
  have frame := copy_frame state effect
  have writes : WritesWithin (copyComponents s) #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨ScalarFrame.workRegion s 2592, by simp, ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  have finalState := ScalarFrame.FrameState.after_effect pre (by decide) state ready frame writes (by simp [copyComponents])
  refine ⟨fuel, u, run, finalState, effect.rip, ?_, frame⟩
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨_, _, h0, h8, h16, h24⟩
  change memLoad u.external (stackPtr t + 0#64) 64 = memLoad t.external (stackPtr t + 120#64) 64 at h0
  change memLoad u.external (stackPtr t + 8#64) 64 = memLoad t.external (stackPtr t + 128#64) 64 at h8
  change memLoad u.external (stackPtr t + 16#64) 64 = memLoad t.external (stackPtr t + 136#64) 64 at h16
  change memLoad u.external (stackPtr t + 24#64) 64 = memLoad t.external (stackPtr t + 144#64) 64 at h24
  have source : stackPtr t + 120 = stackPtr s - 288 := input_stack_address state.rsp (by decide)
  have hx' : MontgomeryAt t (stackPtr t + 120) x := source.symm ▸ hx
  have out := ScalarFrame.stack_readable pre finalState (by decide) (offset := 0) (len := 32) (by decide)
  rw [BitVec.add_zero, finalState.rsp] at out
  apply Field.montgomeryAt_of_memLoad_limbs hx.1 out.mem
  intro j hj
  rw [← hx'.memLoad_limb j hj]
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    first
    | simpa (config := {decide := true}) only [x86_compose, state.rsp, BitVec.add_assoc] using h0
    | simpa (config := {decide := true}) only [x86_compose, state.rsp, BitVec.add_assoc] using h8
    | simpa (config := {decide := true}) only [x86_compose, state.rsp, BitVec.add_assoc] using h16
    | simpa (config := {decide := true}) only [x86_compose, state.rsp, BitVec.add_assoc] using h24

end P256.Proofs.Sec1.Decompress.Cubic
