import Hkdf.Proofs.NewExpand.Extract.Finish.Geometry
import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open CallFrame
open Hkdf.Proofs.Common.Field

private def copyBytes : List UInt8 :=
  [0x4c,0x8d,0xb4,0x24,0x08,0x01,0,0,0x48,0x8d,0x74,0x24,0x78,
   0xba,0x90,0,0,0,0x4c,0x89,0xf7]

private def copyEffect (s : RamState) : Effect :=
  { rip := 0x10fce0
    writes := [⟨(.reg 14 : Operand 64), rspOf s + 264⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 2 : Operand 64), 144⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 264⟩] }

private theorem copy_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10fccb)
      (codeRange 0x10fccb copyBytes) (Effect.post copyEffect) := by
  advance_begin (lea_r64_effect_step 0x10fccb 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xfcd3 (by decide))
  advance_then (lea_r64_effect_step 0x10fcd3 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fccb copyBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfcd8 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10fcd8 0xba (by decide) 144)
  case sub => exact codeRange_slice_subset 0x10fccb copyBytes 13 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfcdd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10fcdd 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fccb copyBytes 18 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfce0 (by decide))⟩
  advance_finish [copyEffect]

private def finalizeBytes : List UInt8 :=
  [0x48,0x8b,0x5c,0x24,0x50,0x48,0x89,0xdf,0x4c,0x89,0xf6]

private def finalizeEffect (s : RamState) : Effect :=
  { rip := 0x10fcf1
    writes := [⟨(.reg 3 : Operand 64), (Operand.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (Operand.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }

private theorem finalize_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10fce6 ∧ MemReadable s (rspOf s + 80) 8)
      (codeRange 0x10fce6 finalizeBytes) (Effect.post finalizeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fce6 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case pre =>
    intro s hs
    exact ⟨hs.1, hs.2⟩
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xfceb (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fceb 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fce6 finalizeBytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfcee (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10fcee 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fce6 finalizeBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfcf1 (by decide))⟩
  advance_finish [finalizeEffect]

private abbrev copyLayout : StackCallLayout 2264 144 144 0 :=
  ⟨464, 336, 192, by decide, by decide, by decide, by decide, by decide, by decide, .inl (by decide)⟩

private theorem stack_base_sub (initial : RamState) :
    base initial + 120 = stackPtr initial - 336 ∧
    base initial + 264 = stackPtr initial - 192 ∧
    base initial + 80 = stackPtr initial - 376 := by
  simp only [base, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, and_self]

private theorem call_pushAddr {initial s : RamState} (rsp : stackPtr s = base initial) :
    pushAddr s = stackPtr initial - 464 := by
  rw [pushAddr, rsp, base, BitVec.sub_sub]
  rfl

private theorem call_bytes {initial s t : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} {offset length : Nat} (rsp : stackPtr s = base initial)
    (call : (callEffect target ret s).Holds s t) (small : length + 8 < 2^64)
    (apart : OffsetsApart (-(BitVec.ofNat 64 offset)) length (-464) 8) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) length).Agrees s t := by
  intro i hi
  apply call.agrees.memory
  intro c hc covers
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact covers.elim
  · obtain ⟨j, hj, he⟩ := covers
    exact OffsetsApart.ne apart (stackPtr initial) hi hj small
      (by simpa only [call_pushAddr rsp, BitVec.sub_eq_add_neg] using he)
  · exact covers.elim

private theorem copy_hmac [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (state : Updated initial s boundary salt ikm) :
    ∃ t, Frame initial t boundary ∧ t.RIP = 0x10fce6 ∧
      t.regValue .r14 = base initial + 264 ∧
      HmacAt t (base initial + 264) (salt.getD (RFC5869.defaultSalt .sha256)) ikm := by
  have avoids : ∀ region ∈ #v[Stack.region initial 2264], region.Avoids InProgram := by
    intro region member a ha hp
    have eq : region = Stack.region initial 2264 := by simpa using member
    rw [eq] at ha
    exact pre.call.stackAvoid a ha (.inl hp)
  obtain ⟨fuel, u, run, ready, _, setup⟩ := copy_setup boundary pre.call.outerBoundary s
    (supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfccb copyBytes
      (by decide) (by decide +kernel)) state.rip
  have noMem : ∀ c ∈ (copyEffect s).components, ∀ a, ¬ c.Covers a := by
    simp [copyEffect, Effect.components, Component.Covers]
  have runningU := state.toRunning.of_agrees run ready setup.agrees
    (fun c hc a ha ↦ (noMem c hc a ha).elim) avoids (by simp [copyEffect, Effect.components])
  have memoryU := setup.agrees.external noMem
  have rspU : stackPtr u = base initial :=
    (setup.agrees.read (n := 64) (r := 4) (by simp [copyEffect, Effect.components])).trans state.rsp
  have values := setup.writes
  change u.regValue .r14 = stackPtr s + 264 ∧ u.regValue .rsi = stackPtr s + 120 ∧
    u.regValue .rdx = 144 ∧ u.regValue .rdi = stackPtr s + 264 at values
  rw [state.rsp] at values
  have pointer := Common.Memory.memcpy_pointer runningU.loaded
  have target : callMemPtr 0x10fce0 (.rip 0xf1632) u = 0x10dd60 := pointer.2
  have push := call_pushAddr rspU
  obtain ⟨a, runningA, called, ret⟩ := runningU.call_stack
    pre.call.stack pre.call.stackAvoid (depth := 456) rspU (by decide) (by decide)
    0xfce0 6 (by decide) setup.rip
    (call_m64_effect_step 0x10fce0 (.rip 0xf1632) (by decide) rfl rfl)
    (programText_slice (programLoaded_codeIn runningU.loaded) 0xfce0
      (encodeCallM64 (.rip 0xf1632)) (by decide) (by decide +kernel))
    (fun pushed ↦ ⟨⟨pushed, by rw [target]; decide⟩, pointer.1⟩)
    (by
      rw [target]
      exact boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide)))
  have rspA : stackPtr a = stackPtr initial - 464 := called.writes.1.trans push
  have outA : a.regValue .rdi = stackPtr initial - 192 :=
    (called.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      (values.2.2.2.trans (stack_base_sub initial).2.1)
  have inA : a.regValue .rsi = stackPtr initial - 336 :=
    (called.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans
      (values.2.1.trans (stack_base_sub initial).1)
  have lenA : a.regValue .rdx = 144 :=
    (called.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans
      values.2.2.1
  have copyPre := callee_pre_of_stack pre.call.stride pre.call.stack pre.call.stackAvoid
    pre.call.outerBoundary runningA.machine runningA.directionFlag runningA.loaded runningA.allocated
    copyLayout (called.rip.trans target) rspA inA outA
    (by rw [ret]; exact inProgram_of_textOffset 0xfce6 (by decide))
  obtain ⟨t, result, copied, _⟩ := Common.Memory.memcpy_correct copyPre lenA (by decide)
  have runningT := runningA.of_callee result (by
    intro region member addr ha
    exact ⟨_, by simp, stack_layout_within pre.call.stack copyLayout rspA outA region member addr ha⟩)
  have setupFrame : MemoryWriteFrame s u #v[registerRegion a .rdi 144, Stack.region a 0] := by
    intro addr outside
    rw [memoryU]
  have pushFrame : MemoryWriteFrame u a #v[registerRegion a .rdi 144, Stack.region a 0] :=
    frame_mono (call_frame copyPre.stack called) (by
      intro region member addr ha
      have eq : region = Stack.region a 0 := by simpa using member
      exact ⟨Stack.region a 0, by simp, eq ▸ ha⟩)
  have copyFrame := memoryWriteFrame_trans setupFrame
    (memoryWriteFrame_trans pushFrame result.frame)
  have spT : stackPtr t = base initial := result.rsp.trans (congrArg ReturnBoundary.rsp ret)
  have frameT : Frame initial t boundary := state.toFrame.of_frame pre.call.stack runningT copyFrame
    (spT.trans state.rsp.symm)
    (result.abi.2.2.1.trans ((called.agrees.mxcsr (by simp [callEffect, pushEffect_components])).trans
      (setup.agrees.mxcsr (by simp [copyEffect, Effect.components]))))
    (result.abi.2.2.2.trans ((called.agrees.fcw (by simp [callEffect, pushEffect_components])).trans
      (setup.agrees.fcw (by simp [copyEffect, Effect.components]))))
    (by
      intro region member
      constructor
      · exact stack_layout_disjoint pre.call.stack copyLayout rspA outA
          (savedOffset := 48) (savedBytes := 56) (.inl (by decide)) (by decide) region member
      · rw [(stack_base_sub initial).2.2]
        exact stack_layout_disjoint pre.call.stack copyLayout rspA outA
          (savedOffset := 376) (savedBytes := 8) (.inr (by decide)) (by decide) region member)
  have srcPush : (Component.mem (stackPtr initial - 336) 144).Agrees u a :=
    call_bytes rspU called (by decide) (by unfold OffsetsApart; decide +kernel)
  have hmacA : HmacAt a (stackPtr initial - 336) (salt.getD (RFC5869.defaultSalt .sha256)) ikm := by
    have hmacS := state.hmac
    rw [(stack_base_sub initial).1] at hmacS
    exact hmacS.of_copy (fun i hi ↦ (srcPush i hi).trans (by rw [memoryU]))
  have hmacT : HmacAt t (base initial + 264) (salt.getD (RFC5869.defaultSalt .sha256)) ikm := by
    rw [(stack_base_sub initial).2.1]
    apply hmacA.of_copy
    intro i hi
    simpa only [outA, inA] using copied i hi
  have r14 : t.regValue .r14 = base initial + 264 :=
    (result.abi.1 .r14 (by simp)).trans
      ((called.agrees.read (n := 64) (r := 14) (by simp [callEffect, pushEffect_components])).trans
        values.1)
  exact ⟨t, frameT, result.rip.trans (congrArg ReturnBoundary.rip ret), r14, hmacT⟩

theorem enter_finalize [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (state : Updated initial s boundary salt ikm) :
    ∃ t, FinalizeCall initial t boundary salt ikm := by
  have avoids : ∀ region ∈ #v[Stack.region initial 2264], region.Avoids InProgram := by
    intro region member a ha hp
    have eq : region = Stack.region initial 2264 := by simpa using member
    rw [eq] at ha
    exact pre.call.stackAvoid a ha (.inl hp)
  obtain ⟨a, frameA, ripA, r14, hmacA⟩ := copy_hmac pre state
  have runningA := frameA.toRunning
  have rspA := frameA.rsp
  have readable : MemReadable a (rspOf a + 80) 8 := by
    rw [show rspOf a = base initial from rspA, (stack_base_sub initial).2.2]
    exact stack_readable pre.call.stack runningA.allocated (by decide) (by decide)
  obtain ⟨fuel, u, run, ready, _, setup⟩ := finalize_setup boundary pre.call.outerBoundary a
    (supportedMachine_readyToStep runningA.machine)
    (programText_slice (programLoaded_codeIn runningA.loaded) 0xfce6 finalizeBytes
      (by decide) (by decide +kernel)) ⟨ripA, readable⟩
  have noMem : ∀ c ∈ (finalizeEffect a).components, ∀ addr, ¬ c.Covers addr := by
    simp [finalizeEffect, Effect.components, Component.Covers]
  have runningU := runningA.of_agrees run ready setup.agrees
    (fun c hc addr ha ↦ (noMem c hc addr ha).elim) avoids
    (by simp [finalizeEffect, Effect.components])
  have memoryU := setup.agrees.external noMem
  have rspU : stackPtr u = base initial :=
    (setup.agrees.read (n := 64) (r := 4) (by simp [finalizeEffect, Effect.components])).trans rspA
  have values := setup.writes
  change u.regValue .rbx = memLoad a.external (rspOf a + 80) 64 ∧
    u.regValue .rdi = memLoad a.external (rspOf a + 80) 64 ∧
    u.regValue .rsi = a.regValue .r14 at values
  rw [show rspOf a = base initial from rspA, frameA.outputPtr, r14] at values
  have push := call_pushAddr rspU
  have step : StepEffect (PushPre 0x10fcf1 5)
      (codeRange 0x10fcf1 (encodeCallRel32 0xffffe09a))
      (callEffect (fun _ ↦ 0x10dd90) 0x10fcf6) :=
    call_rel32_effect_step 0x10fcf1 0xffffe09a (by decide +kernel)
  obtain ⟨t, runningT, called, ret⟩ := runningU.call_stack
    pre.call.stack pre.call.stackAvoid (depth := 456) rspU (by decide) (by decide)
    0xfcf1 5 (by decide) setup.rip step
    (programText_slice (programLoaded_codeIn runningU.loaded) 0xfcf1
      (encodeCallRel32 0xffffe09a) (by decide) (by decide +kernel))
    id (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xdd90 (by decide)))
  have savedPush : (Component.mem (stackPtr initial - 48) 56).Agrees u t :=
    call_bytes rspU called (by decide) (by unfold OffsetsApart; decide +kernel)
  have savedBytes : (Component.mem (stackPtr initial - 48) 56).Agrees a t := by
    intro i hi
    exact (savedPush i hi).trans (by rw [memoryU])
  have saved := frameA.toSaved.of_agrees savedBytes
    ((called.agrees.mxcsr (by simp [callEffect, pushEffect_components])).trans
      (setup.agrees.mxcsr (by simp [finalizeEffect, Effect.components])))
    ((called.agrees.fcw (by simp [callEffect, pushEffect_components])).trans
      (setup.agrees.fcw (by simp [finalizeEffect, Effect.components])))
  have input : t.regValue .rsi = base initial + 264 :=
    (called.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans
      values.2.2
  have output : t.regValue .rdi = initial.regValue .rdi :=
    (called.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      values.2.1
  have hmac : HmacAt t (t.regValue .rsi) (salt.getD (RFC5869.defaultSalt .sha256)) ikm := by
    rw [input, (stack_base_sub initial).2.1]
    rw [(stack_base_sub initial).2.1] at hmacA
    have same : (Component.mem (stackPtr initial - 192) 144).Agrees u t :=
      call_bytes rspU called (by decide) (by unfold OffsetsApart; decide +kernel)
    exact hmacA.of_copy (fun i hi ↦ (same i hi).trans (by rw [memoryU]))
  exact ⟨t, runningT, saved, called.writes.1.trans push, input, output,
    ret, called.rip, hmac⟩

end Hkdf.Proofs.NewExpand.Extract
