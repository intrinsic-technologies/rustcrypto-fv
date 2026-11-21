import P256.Proofs.Verifying.Combination.Table.State
import P256.Proofs.Program.Code
import P256.Proofs.Program.Push
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Program (readyToStep supportedMachine_of_ready_agrees
  programText_slice programLoaded_codeIn boundary_ne_program inProgram_of_textOffset ScalarFrame.stack_contains)
open P256.Proofs.Program (push_exists)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def saveMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore s.external
    (stackPtr s - 8) (s.regValue .r15))
    (stackPtr s - 16) (s.regValue .r14))
    (stackPtr s - 24) (s.regValue .r12))
    (stackPtr s - 32) (s.regValue .rbx)

def saveFrame (s : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8]

set_option maxHeartbeats 600000 in
theorem save_registers [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10aff7 ∧ stackPtr t = stackPtr s - 32 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s) s t := by
  obtain ⟨s1, ha1, hr1, hl1, hip1, hsp1, hfstep1, hm1⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 15 0 0xaff0
      (by simp only [BitVec.sub_zero]) pre.rip (by decide) (by decide)
      (by decide +kernel) (by decide +kernel)
  have hf1 := hfstep1
  obtain ⟨s2, ha2, hr2, hl2, hip2, hsp2, hfstep2, hm2⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary hr1 hl1 hf1.grow 14 8 0xaff2
      hsp1 hip1 (by decide) (by decide)
      (by decide +kernel) (by decide +kernel)
  have hf2 := hf1.trans hfstep2
  obtain ⟨s3, ha3, hr3, hl3, hip3, hsp3, hfstep3, hm3⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary hr2 hl2 hf2.grow 12 16 0xaff4
      hsp2 hip2 (by decide) (by decide)
      (by decide +kernel) (by decide +kernel)
  have hf3 := hf2.trans hfstep3
  obtain ⟨s4, ha4, hr4, hl4, hip4, hsp4, hfstep4, hm4⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary hr3 hl3 hf3.grow 3 24 0xaff6
      hsp3 hip3 (by decide) (by decide)
      (by decide +kernel) (by decide +kernel)
  have hf4 := hf3.trans hfstep4
  refine ⟨s4, ((ha1.trans ha2).trans ha3).trans ha4, hr4, hl4, hip4, hsp4, ?_, ?_⟩
  · have hv1 : (Operand.reg 15 : Operand 64).read s = s.regValue .r15 := rfl
    have hv2 : (Operand.reg 14 : Operand 64).read s1 = s.regValue .r14 := hf1.read (by simp)
    have hv3 : (Operand.reg 12 : Operand 64).read s2 = s.regValue .r12 := hf2.read (by simp)
    have hv4 : (Operand.reg 3 : Operand 64).read s3 = s.regValue .rbx := hf3.read (by simp)
    rw [hm4, hm3, hm2, hm1]
    simp only [show BitVec.setWidth 5 (15 : BitVec 4) = (15 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (14 : BitVec 4) = (14 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (12 : BitVec 4) = (12 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (3 : BitVec 4) = (3 : BitVec 5) from rfl, hv1, hv2, hv3, hv4]
    rfl
  · apply hf4.mono
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (((h | h) | h) | h) <;>
      rcases h with rfl | rfl | rfl <;> simp

theorem saveMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (hentry : entry ∈ savedRegisters) :
    memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 =
      s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl
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
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point) :
    ∃ t, Advances boundary 5 s t ∧ FrameState s t cursor ∧ t.RIP = 0x10affe ∧
      t.external = saveMemory s ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ := save_registers pre
  obtain ⟨t, step, ready', effect⟩ :=
    (sub_r64_imm32_effect_step 0x10aff7 0x48 0xec 1064
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xaff7
        [0x48,0x81,0xec,0x28,0x04,0,0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xaffe (by decide)))
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
      #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120] := by
    intro c hc a covered
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨_, by simp,
      ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) covered⟩
  refine ⟨t, run.trans step, ⟨P256.Proofs.Program.bindingsSupported_of_ready_agrees pre.bindingsSupported ready' frame,
    supportedMachine_of_ready_agrees pre.machine ready' frame,
    ?_, frame.directionFlagClear (by component_not_mem) pre.directionFlag, frame.grow, frame.memoryWriteFrame writes,
    ?_, ?_, ?_, ?_, ?_, frame.mxcsr (by component_not_mem), frame.fcw (by component_not_mem)⟩,
    effect.rip, mem, frame⟩
  · intro a b hb
    rw [ext]
    exact loaded a b hb
  · have hw : stackPtr t = stackPtr u - 1064 := effect.writes
    rw [hw, rsp, BitVec.sub_sub]
    rfl
  · intro entry he
    change memLoad t.external _ 64 = _
    rw [mem]
    exact saveMemory_saved s entry he
  · exact frame.read (n := 64) (r := 5) (by simp [saveFrame])
  · exact frame.read (n := 64) (r := 13) (by simp [saveFrame])
  · change memLoad t.external _ 64 = _
    rw [mem]
    exact saveMemory_return s

end P256.Proofs.Verifying.Combination.Table
