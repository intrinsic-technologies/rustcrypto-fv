import P256.Proofs.Verifying.Combination.InitialCopy
import P256.Proofs.Verifying.Combination.Preparation.PointerState
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pointer_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (agrees : AgreesExcept [.mem (stackPtr s - 6496) 8, .mem (stackPtr s - 6480) 8,
      .mem (stackPtr s - 6488) 8, .mem (stackPtr s - 6520) 8,
      .reg 0, .reg 5, .reg 15, .reg 6, .reg 7, .rip] t u)
    {off len i : Nat} (ho : off ≤ 8808) (hl : len ≤ off + 8)
    (apart : ∀ dst ∈ [6496, 6480, 6488, 6520], off + 8 ≤ dst ∨ dst + len ≤ off)
    (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals
    obtain ⟨j, hj, he⟩ := hv
    exact stack_sub_apart pre.stack (by decide) ho (by decide) hl
      (apart _ (by simp)) j hj i hi he.symm

theorem zero_index [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x10657d) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x10657f ∧
      AgreesExcept [.reg 2, .flags, .rip] t u := by
  obtain ⟨u, run, ready, effect⟩ := (xor_r32_r32_effect_step 0x10657d 0xd2 rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x657d _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x657f (by decide)))
  have agrees : AgreesExcept [.reg 2, .flags, .rip] t u := effect.agrees
  exact ⟨u, run, state.after_registers ready agrees (by simp [Component.Covers])
    (by simp), effect.rip, agrees⟩

structure FirstTableInput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552 where
  rip : t.RIP = 0x10657f
  values : InputAt t (stackPtr s - 5472) p q u v
  input : t.regValue .rsi = stackPtr s - 6520
  output : t.regValue .rdi = stackPtr s - 4656
  temporary : t.regValue .rbp = stackPtr s - 4656
  original : t.regValue .r15 = stackPtr s - 6520
  target : t.regValue .r14 = 0x11c930
  cursor : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496
  point : memLoad t.external (stackPtr s - 6496) 64 = stackPtr s - 5472
  savedInput : memLoad t.external (stackPtr s - 6544) 64 = s.regValue .rsi
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem first_table_input [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : InputAt s (s.regValue .rsi) p q u v) :
    ∃ fuel t, Advances boundary fuel s t ∧ FirstTableInput s t p q u v := by
  obtain ⟨n, a, runA, stateA, ripA, valuesA, rbxA, rbpA, r15A, outputA⟩ := initial_copy pre input
  obtain ⟨m, b, runB, stateB, ripB, agreesB⟩ := table_pointer pre stateA ripA rbxA
  have valuesB := valuesA.of_bytes_eq (fun _ hi => pointer_byte pre agreesB
    (by decide) (by decide) (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) hi)
  have originalB : memLoad b.external (stackPtr s - 6544) 64 = s.regValue .rsi := by
    refine Eq.trans ?_ r15A
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (pointer_byte pre agreesB
      (off := 6544) (len := 8) (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) hi)
  have outputB : memLoad b.external (stackPtr s - 6536) 64 = s.regValue .rdi := by
    refine Eq.trans ?_ outputA
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (pointer_byte pre agreesB
      (off := 6536) (len := 8) (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) hi)
  obtain ⟨t, runT, stateT, ripT, agreesT⟩ := zero_index pre stateB.toFrameState ripB
  have memory := agreesT.external (by simp [Component.Covers])
  refine ⟨n+m+1, t, (runA.trans runB).trans runT, stateT, ripT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact valuesB.of_bytes_eq (fun _ _ => congrArg (fun ram : Ram => ram[_]?) memory)
  · exact (agreesT.read (n := 64) (r := 6) (by simp)).trans stateB.input
  · exact (agreesT.read (n := 64) (r := 7) (by simp)).trans stateB.output
  · exact (agreesT.read (n := 64) (r := 5) (by simp)).trans stateB.temporary
  · exact (agreesT.read (n := 64) (r := 15) (by simp)).trans
      stateB.iterator
  · exact (agreesT.read (n := 64) (r := 14) (by simp)).trans
      ((agreesB.read (n := 64) (r := 14) (by simp)).trans rbpA)
  · rw [memory]; exact stateB.cursorPointer
  · rw [memory]; exact stateB.pointPointer
  · rw [memory]; exact originalB
  · rw [memory]; exact outputB

end P256.Proofs.Verifying.Combination.Preparation
