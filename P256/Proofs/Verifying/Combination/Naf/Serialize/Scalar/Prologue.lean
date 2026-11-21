import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Program (readyToStep supportedMachine_of_ready_agrees
  programText_slice programLoaded_codeIn boundary_ne_program inProgram_of_textOffset ScalarFrame.stack_contains)
open P256.Proofs.Program (push_exists)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def saveMemory (s : RamState) : Ram :=
  memStore (memStore s.external (stackPtr s - 8) (s.regValue .r14))
    (stackPtr s - 16) (s.regValue .rbx)

def saveFrame (s : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8]

theorem save_registers [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10b173 ∧ stackPtr t = stackPtr s - 16 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s) s t := by
  obtain ⟨s1, run1, ready1, loaded1, rip1, sp1, ag1, mem1⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (fun _ h => h) 14 0 0xb170 (by simp only [BitVec.sub_zero]) pre.rip
      (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  obtain ⟨s2, run2, ready2, loaded2, rip2, sp2, ag2, mem2⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready1 loaded1 ag1.grow 3 8 0xb172 sp1 rip1
      (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  refine ⟨s2, run1.trans run2, ready2, loaded2, rip2, sp2, ?_, ?_⟩
  · have v1 : (Operand.reg 14 : Operand 64).read s = s.regValue .r14 := rfl
    have v2 : (Operand.reg 3 : Operand 64).read s1 = s.regValue .rbx := ag1.read (by simp)
    rw [mem2, mem1]
    simp only [show BitVec.setWidth 5 (14 : BitVec 4) = (14 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (3 : BitVec 4) = (3 : BitVec 5) from rfl, v1, v2]
    rfl
  · apply (ag1.trans ag2).mono
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (h | h) <;> rcases h with rfl | rfl | rfl <;> simp

theorem saveMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (hentry : entry ∈ savedRegisters) :
    memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 =
      s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl
  all_goals
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

theorem saveMemory_return (s : RamState) :
    memLoad (saveMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  simp only [saveMemory, BitVec.sub_eq_add_neg]
  conv => lhs; arg 2; rw [← BitVec.add_zero (stackPtr s)]
  repeat rw [memLoad_memStore_apart _ _ _ _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  rw [BitVec.add_zero]

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point) :
    ∃ t, Advances boundary 3 s t ∧ FrameState s t cursor ∧ t.RIP = 0x10b17a ∧
      t.external = saveMemory s ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ := save_registers pre
  obtain ⟨t, step, ready', effect⟩ :=
    (sub_r64_imm32_effect_step 0x10b173 0x48 0xec 344
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xb173
        [0x48,0x81,0xec,0x58,0x01,0,0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb17a (by decide)))
  have ext : t.external = u.external := effect.agrees.external (by simp [Component.Covers])
  have mem : t.external = saveMemory s := ext.trans memory
  have frame : AgreesExcept (saveFrame s ++ [.flags]) s t := by
    apply (agrees.trans effect.agrees).mono
    simp only [saveFrame, subR64Imm32Effect_components, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact .inl h
    · exact .inl (.inl rfl)
    · exact .inr rfl
    · exact .inl (.inr (.inl rfl))
  have writes : WritesWithin (saveFrame s ++ [.flags])
      #v[registerRegion s .rdi 272, cursorRegion cursor, Stack.region s 536] := by
    intro c hc a covered
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨_, by simp,
      P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) covered⟩
  refine ⟨t, run.trans step, ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready' frame,
    supportedMachine_of_ready_agrees pre.machine ready' frame,
    ?_, frame.directionFlagClear (by component_not_mem) pre.directionFlag, frame.grow, frame.memoryWriteFrame writes,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.mxcsr (by component_not_mem), frame.fcw (by component_not_mem)⟩,
    effect.rip, mem, frame⟩
  · intro a b hb
    rw [ext]
    exact loaded a b hb
  · have hw : stackPtr t = stackPtr u - 344 := effect.writes
    rw [hw, rsp, BitVec.sub_sub]
    rfl
  · intro entry he
    change memLoad t.external _ 64 = _
    rw [mem]
    exact saveMemory_saved s entry he
  · exact frame.read (n := 64) (r := 5) (by simp [saveFrame])
  · exact frame.read (n := 64) (r := 12) (by simp [saveFrame])
  · exact frame.read (n := 64) (r := 13) (by simp [saveFrame])
  · exact frame.read (n := 64) (r := 15) (by simp [saveFrame])
  · change memLoad t.external _ 64 = _
    rw [mem]
    exact saveMemory_return s

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
