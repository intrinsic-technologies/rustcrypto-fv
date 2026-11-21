import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Memory
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Serialize

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem serialize_run [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) (rip : t.RIP = 0x1022b7) :
    ∃ fuel u, Advances (returnBoundary initial) fuel t u ∧ State initial u ∧
      u.RIP = 0x102317 ∧
      MemoryWriteFrame t u #v[registerRegion initial .rcx 72] ∧
      ∀ part : Bool, ∀ j < 4, memLoad u.external (initial.regValue .rcx + (if part then 40 else 8) + BitVec.ofNat 64 (8*j)) 64 =
        bswap64 (memLoad t.external (stackPtr t + (if part then 40 else 8) + BitVec.ofNat 64 (8*(3-j))) 64) := by
  have hp : SerializePre t := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · intro off ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact stack_readable pre state (by decide)
    · intro off ho
      change CrossPageStore.Writable t (t.regValue .rbx + BitVec.ofNat 64 off) 8
      rw [state.output]
      apply (output_writable pre state).add off
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro off ho offset len hb
      change RangeApart (t.regValue .rbx + BitVec.ofNat 64 off) 8 _ _
      rw [state.output]
      apply RangeApart.add_left (h := output_code pre hb) off
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨n,u,run,ready,_,effect⟩ := serialize (returnBoundary initial) pre.outside t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x22b7 serializeBytes
      (by decide) (by decide +kernel)) hp
  have hout : (Operand.reg 3 : Operand 64).read t = initial.regValue .rcx := state.output
  have f : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
      .mem (initial.regValue .rcx + 8#64) 8, .mem (initial.regValue .rcx + 16#64) 8,
      .mem (initial.regValue .rcx + 24#64) 8, .mem (initial.regValue .rcx + 32#64) 8,
      .mem (initial.regValue .rcx + 40#64) 8,.mem (initial.regValue .rcx + 48#64) 8,
      .mem (initial.regValue .rcx + 56#64) 8,.mem (initial.regValue .rcx + 64#64) 8,.rip] t u := by
    simpa only [serializeEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append, hout] using effect.agrees
  have writes : WritesWithin [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
      .mem (initial.regValue .rcx + 8#64) 8, .mem (initial.regValue .rcx + 16#64) 8,
      .mem (initial.regValue .rcx + 24#64) 8, .mem (initial.regValue .rcx + 32#64) 8,
      .mem (initial.regValue .rcx + 40#64) 8,.mem (initial.regValue .rcx + 48#64) 8,
      .mem (initial.regValue .rcx + 56#64) 8,.mem (initial.regValue .rcx + 64#64) 8,.rip]
      #v[registerRegion initial .rcx 72] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨_, by simp, output_contains pre (off := 8) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 16) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 24) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 32) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 40) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 48) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 56) (by decide) ha⟩
    · exact ⟨_, by simp, output_contains pre (off := 64) (by decide) ha⟩
  refine ⟨n,u,run,after pre state ready f writes (by simp) (by simp),effect.rip,
    f.memoryWriteFrame writes, ?_⟩
  rcases effect.writes with ⟨_,_,_,_,_,_,_,_,h0,h1,h2,h3,h4,h5,h6,h7⟩
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 8#64) 64 = _ at h0
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 16#64) 64 = _ at h1
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 24#64) 64 = _ at h2
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 32#64) 64 = _ at h3
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 40#64) 64 = _ at h4
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 48#64) 64 = _ at h5
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 56#64) 64 = _ at h6
  change memLoad u.external ((Operand.reg 3 : Operand 64).read t + 64#64) 64 = _ at h7
  rw [hout] at h0 h1 h2 h3 h4 h5 h6 h7
  intro part j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  cases part <;> rcases cases with rfl | rfl | rfl | rfl
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, Nat.reduceSub, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success
