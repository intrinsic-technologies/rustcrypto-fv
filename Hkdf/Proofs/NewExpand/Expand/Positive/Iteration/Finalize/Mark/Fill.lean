import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine.StackRegion
import Hkdf.Proofs.Common.Memory.Fill
import Hkdf.Proofs.Common.Memory.Pointers

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

private def fillLayout (position : Nat) (bound : position ≤ 64) :
    StackCallLayout 2264 0 (64 - position) 0 :=
  ⟨544, 536, 456 - position, by decide, by decide, by decide, by omega, by omega, by omega,
    .inl (by omega)⟩

theorem local_address {entry s : RamState} (rsp : stackPtr s = stackPtr entry - 536)
    (offset : Nat) (bound : offset ≤ 536) :
    stackPtr s + BitVec.ofNat 64 offset = stackPtr entry - BitVec.ofNat 64 (536 - offset) := by
  have sum : BitVec.ofNat 64 536 =
      BitVec.ofNat 64 (536 - offset) + BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel bound]
  rw [rsp]
  change stackPtr entry - BitVec.ofNat 64 536 + BitVec.ofNat 64 offset = _
  rw [sum, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem fill_run [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {n position : Nat} {regions : Vector MemoryRegion n}
    (stack : Stack.Valid entry 2264)
    (avoid : (Stack.region entry 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (stackIn : Stack.region entry 2264 ∈ regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram)
    (outside : ¬ InProgram boundary.rip) (stride : UnitStringStride bindings)
    (running : Running entry boundary regions s)
    (rsp : stackPtr s = stackPtr entry - 536) (bound : position ≤ 64)
    (rip : s.RIP = 0x10f985)
    (destination : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 (80 + position))
    (zero : s.regValue .rsi = 0)
    (length : s.regValue .rdx = BitVec.ofNat 64 (64 - position)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Running entry boundary regions t ∧
      t.RIP = 0x10f98b ∧ stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[
        ⟨(stackPtr s + BitVec.ofNat 64 (80 + position)).toNat, 64 - position⟩,
        ⟨(stackPtr s - 8).toNat, 8⟩] ∧
      (∀ i < 64 - position,
        t.external[stackPtr s + BitVec.ofNat 64 (80 + position) + BitVec.ofNat 64 i]? = some 0) := by
  have pointer := Hkdf.Proofs.Common.Memory.memset_pointer running.loaded
  have target : callMemPtr 0x10f985 (.rip 0xf19ad) s = 0x10dd10 := pointer.2
  have push : pushAddr s = stackPtr entry - 544 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 stack avoid running.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 0x10f985 6 := by
    rw [push]
    exact stack_codeApart (offset := 544) (codeOffset := 0xf985) stack
      (fun a ha hp ↦ avoid a ha (.inl hp)) (by decide) (by decide) (by decide)
  have step := call_m64_effect_step 0x10f985 (.rip 0xf19ad) (by decide) rfl rfl
  have instruction : CodeIn (codeRange 0x10f985 (encodeCallM64 (.rip 0xf19ad))) s :=
    programText_slice (programLoaded_codeIn running.loaded) 0xf985 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨c, runC, readyC, called⟩ := step.advances
    (supportedMachine_readyToStep running.machine) instruction
    ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointer.1⟩
    (boundary := boundary)
    (by
      change callMemPtr 0x10f985 (.rip 0xf19ad) s ≠ boundary.rip
      rw [target]
      exact boundary_ne_program outside (inProgram_of_textOffset 0xdd10 (by decide)))
  have callFrame : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s c := by
    simpa only [callEffect, pushEffect_components] using called.agrees
  have runningC := running.of_agrees runC readyC callFrame (by
    intro component member a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · rw [push] at covered
      exact ⟨_, stackIn, stackRegion_contains_sub stack.2.2.1
        (by decide : 544 ≤ 2264) (by decide : 8 ≤ 544) covered⟩
    · exact covered.elim) avoids (by simp)
  have rspC : stackPtr c = stackPtr entry - 544 := called.writes.1.trans push
  have boundaryC : returnBoundary c = ⟨0x10f98b, stackPtr s⟩ := call_boundary called
  have outputC : c.regValue .rdi = stackPtr s + BitVec.ofNat 64 (80 + position) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination
  have zeroC : c.regValue .rsi = 0 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans zero
  have lengthC : c.regValue .rdx = BitVec.ofNat 64 (64 - position) :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  have outputAddress : c.regValue .rdi = stackPtr entry - BitVec.ofNat 64 (456 - position) :=
    outputC.trans ((local_address rsp (80 + position) (by omega)).trans
      (by rw [show 536 - (80 + position) = 456 - position by omega]))
  have hp : CalleePre c boundary 0x10dd10 0 (64 - position) 0 := by
    apply callee_pre_of_stack_output stride stack avoid outside
      runningC.machine runningC.directionFlag runningC.loaded runningC.allocated
      (fillLayout position bound) (called.rip.trans target) rspC outputAddress
    · rw [boundaryC]
      exact inProgram_of_textOffset 0xf98b (by decide)
    · change (c.regValue .rsi).toNat + 0 < 2^32
      rw [zeroC]
      decide
    · intro a ha
      change (c.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (c.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha
      change (c.regValue .rsi).toNat ≤ a ∧ a < (c.regValue .rsi).toNat + 0 at ha
      omega
  obtain ⟨t, result, filled, _⟩ := Hkdf.Proofs.Common.Memory.memset_zero_correct hp
    (by rw [zeroC]; rfl) lengthC (by omega)
  obtain ⟨fuel, exec⟩ := result.execution
  have runningT := runningC.of_callee result (by
    intro region member a contains
    exact ⟨_, stackIn, stack_layout_within stack (fillLayout position bound)
      rspC outputAddress region member a contains⟩)
  have complete := call_result hp called result running.directionFlag
  have stackRegion : Stack.region c 0 = ⟨(stackPtr s - 8).toNat, 8⟩ := by
    have same : stackPtr c = stackPtr s - 8 := called.writes.1
    have endRegion := stack_region_end c 0
    change (Stack.region c 0).start + (Stack.region c 0).size = (stackPtr c).toNat + 8 at endRegion
    have startRegion : (Stack.region c 0).start = (stackPtr c).toNat := by
      change (stackPtr c).toNat - 0 = _
      exact Nat.sub_zero _
    have sizeRegion : (Stack.region c 0).size = 8 := by omega
    cases h : Stack.region c 0 with
    | mk start size =>
      rw [h] at startRegion sizeRegion
      change start = (stackPtr c).toNat at startRegion
      change size = 8 at sizeRegion
      rw [startRegion, same, sizeRegion]
  refine ⟨1 + fuel, t, runC.trans exec, runningT, ?_, ?_, complete.2, ?_, ?_⟩
  · rw [result.rip, boundaryC]
  · exact result.rsp.trans (congrArg ReturnBoundary.rsp boundaryC)
  · simpa only [registerRegion, outputC, stackRegion] using complete.1
  · intro i hi
    simpa only [outputC] using filled i hi

end Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding
