import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Encoding.Serialize.Push
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Hmac

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Field


def savedMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore (memStore s.external
    (stackPtr s - 8) (s.regValue .r15))
    (stackPtr s - 16) (s.regValue .r14))
    (stackPtr s - 24) (s.regValue .r13))
    (stackPtr s - 32) (s.regValue .r12))
    (stackPtr s - 40) (s.regValue .rbx)

def savedComponents (s : RamState) : List Component :=
  [.reg 4, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8,
    .mem (stackPtr s - 40) 8, .rip]

theorem save [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264) :
    ∃ s, Advances boundary 5 initial s ∧ ReadyToStep s ∧ ProgramLoaded s ∧
      s.RIP = 0x10dd99 ∧ stackPtr s = stackPtr initial - 40 ∧
      s.external = savedMemory initial ∧ AgreesExcept (savedComponents initial) initial s := by
  obtain ⟨s1, a1, r1, l1, ip1, sp1, f1, m1⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.push_exists pre
      (supportedMachine_readyToStep pre.machine) pre.loaded (fun _ h ↦ h)
      15 0 0xdd90 (by simp only [BitVec.sub_zero]) pre.rip
      (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨s2, a2, r2, l2, ip2, sp2, f2, m2⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.push_exists pre r1 l1 f1.grow
      14 8 0xdd92 sp1 ip1 (by decide) (by decide) (by decide) (by decide +kernel)
  have h2 := f1.trans f2
  obtain ⟨s3, a3, r3, l3, ip3, sp3, f3, m3⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.push_exists pre r2 l2 h2.grow
      13 16 0xdd94 sp2 ip2 (by decide) (by decide) (by decide) (by decide +kernel)
  have h3 := h2.trans f3
  obtain ⟨s4, a4, r4, l4, ip4, sp4, f4, m4⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.push_exists pre r3 l3 h3.grow
      12 24 0xdd96 sp3 ip3 (by decide) (by decide) (by decide) (by decide +kernel)
  have h4 := h3.trans f4
  obtain ⟨s5, a5, r5, l5, ip5, sp5, f5, m5⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.push_exists pre r4 l4 h4.grow
      3 32 0xdd98 sp4 ip4 (by decide) (by decide) (by decide) (by decide +kernel)
  have h5 := h4.trans f5
  refine ⟨s5, (((a1.trans a2).trans a3).trans a4).trans a5, r5, l5, ip5, sp5, ?_, ?_⟩
  · have v1 : (Operand.reg (BitVec.setWidth 5 (15 : BitVec 4)) : Operand 64).read initial =
        initial.regValue .r15 := rfl
    have v2 : (Operand.reg (BitVec.setWidth 5 (14 : BitVec 4)) : Operand 64).read s1 =
        initial.regValue .r14 := f1.read (by simp)
    have v3 : (Operand.reg (BitVec.setWidth 5 (13 : BitVec 4)) : Operand 64).read s2 =
        initial.regValue .r13 := h2.read (by simp)
    have v4 : (Operand.reg (BitVec.setWidth 5 (12 : BitVec 4)) : Operand 64).read s3 =
        initial.regValue .r12 := h3.read (by simp)
    have v5 : (Operand.reg (BitVec.setWidth 5 (3 : BitVec 4)) : Operand 64).read s4 =
        initial.regValue .rbx := h4.read (by simp)
    rw [m5, m4, m3, m2, m1, v1, v2, v3, v4, v5]
    rfl
  · apply h5.mono
    simp only [savedComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;> simp


def setupBytes : List UInt8 :=
  [0x48,0x81,0xec,0x70,1,0,0,0x48,0x89,0xfb,0x48,0x8d,0x7c,0x24,0x48,
    0xba,0x90,0,0,0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10ddad
    writes := [⟨(.reg 4 : Operand 64), rspOf s - 368⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 7 : Operand 64), rspOf s - 296⟩,
      ⟨(.reg 2 : Operand 64), 144⟩]
    flags := some (.ofStatusFlags (subSpec (rspOf s) 368).2) }

theorem setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10dd99 setupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xdd99 setupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10dd99)
      (codeRange 0x10dd99 setupBytes) (Effect.post setupEffect) := by
  advance_begin (show StepEffect _ _ (subR64Imm32Effect 0x10dd99 4 368) from
    sub_r64_imm32_effect_step 0x10dd99 0x48 0xec 368 (by simp [RexWPrefix]) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xdda0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10dda0 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dd99 setupBytes 7 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xdda3 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10dda3 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd99 setupBytes 10 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xdda8 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10dda8 0xba (by decide) 144)
  case sub => exact codeRange_slice_subset 0x10dd99 setupBytes 15 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xddad (by decide))⟩
  advance_finish [setupEffect, BitVec.sub_eq_add_neg, BitVec.add_assoc]


abbrev copyLayout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 1264 0 144 0 :=
  ⟨416, 0, 336, by decide, by decide, by decide, by decide, by decide,
    by decide, .inr (by decide)⟩

theorem copy_input [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (hmac : HmacAt initial (initial.regValue .rsi) key message) :
    ∃ t, Running initial boundary
        #v[registerRegion initial .rdi 176, Stack.region initial 1264] t ∧
      t.RIP = 0x10ddb3 ∧ stackPtr t = stackPtr initial - 408 ∧
      t.regValue .rbx = initial.regValue .rdi ∧
      HmacAt t (stackPtr initial - 336) key message ∧
      (∀ i < 48, t.external[stackPtr initial - 40 + BitVec.ofNat 64 i]? =
        (savedMemory initial)[stackPtr initial - 40 + BitVec.ofNat 64 i]?) ∧
      t.regValue .rbp = initial.regValue .rbp ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  have avoid : ∀ region ∈ #v[registerRegion initial .rdi 176, Stack.region initial 1264],
      region.Avoids InProgram := by
    intro region member a contains inside
    exact pre.avoids region (by simpa using member) a contains (.inl inside)
  obtain ⟨s, saveRun, readyS, loadedS, ripS, rspS, memoryS, saveFrame⟩ := save pre
  have initialRun : Running initial boundary
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] initial :=
    Running.initial pre.machine pre.loaded pre.directionFlag
  have writes : WritesWithin (savedComponents initial)
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] := by
    intro c hc a ha
    simp only [savedComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨Stack.region initial 1264, by simp,
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub pre.stack.2.2.1
        (by decide) (by decide) ha⟩
  have runningS := initialRun.of_agrees saveRun readyS saveFrame writes avoid
    (by simp [savedComponents])
  obtain ⟨fuel, u, setupRun, readyU, _, setup⟩ := setup_run boundary pre.outerBoundary s
    readyS (setup_code loadedS) ripS
  have noMem : ∀ c ∈ (setupEffect s).components, ∀ a, ¬ c.Covers a := by
    simp [setupEffect, Effect.components, Component.Covers]
  have runningU := runningS.of_agrees setupRun readyU setup.agrees
    (fun c hc a ha ↦ (noMem c hc a ha).elim) avoid
    (by simp [setupEffect, Effect.components])
  have setupValues := setup.writes
  change stackPtr u = stackPtr s - 368 ∧ u.regValue .rbx = s.regValue .rdi ∧
    u.regValue .rdi = stackPtr s - 296 ∧ u.regValue .rdx = 144 at setupValues
  have rspU : stackPtr u = stackPtr initial - 408 := by
    rw [setupValues.1, rspS, BitVec.sub_sub]
    rfl
  have outputU : u.regValue .rdi = stackPtr initial - 336 := by
    rw [setupValues.2.2.1, rspS, BitVec.sub_sub]
    rfl
  have inputU : u.regValue .rsi = initial.regValue .rsi :=
    (setup.agrees.read (n := 64) (r := 6) (by simp [setupEffect, Effect.components])).trans
      (saveFrame.read (n := 64) (r := 6) (by simp [savedComponents]))
  have bxU : u.regValue .rbx = initial.regValue .rdi := setupValues.2.1.trans
    (saveFrame.read (n := 64) (r := 7) (by simp [savedComponents]))
  have pushed : pushAddr u = stackPtr initial - 416 := by
    rw [pushAddr, rspU, BitVec.sub_sub]
    rfl
  have stackAvoid := pre.avoids (Stack.region initial 1264) (by simp)
  have writable : MemWritable u (pushAddr u) 8 := by
    rw [pushed]
    exact stack_writable8 pre.stack stackAvoid runningU.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr u) 8 0x10ddad 6 := by
    rw [pushed]
    exact stack_codeApart pre.stack (fun a ha hp ↦ stackAvoid a ha (.inl hp))
      (offset := 416) (len := 8) (codeOffset := 0xddad) (codeLen := 6)
      (by decide) (by decide) (by decide)
  have pointer := Common.Memory.memcpy_pointer runningU.loaded
  have target : callMemPtr 0x10ddad (.rip 0xf3565) u = 0x10dd60 := pointer.2
  have instruction := programText_slice (programLoaded_codeIn runningU.loaded) 0xddad
    (encodeCallM64 (.rip 0xf3565)) (by decide +kernel) (by decide +kernel)
  obtain ⟨a, runningA, call, boundaryA⟩ := runningU.call
    (call_m64_effect_step 0x10ddad (.rip 0xf3565) (by decide) rfl rfl)
    instruction ⟨⟨⟨setup.rip, writable, apart⟩, by rw [target]; decide⟩, pointer.1⟩
    (by
      rw [target]
      exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide)))
    (by
      intro c hc a ha
      simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ha.elim
      · rw [pushed] at ha
        exact ⟨Stack.region initial 1264, by simp,
          Hkdf.Proofs.Common.Machine.stackRegion_contains_sub pre.stack.2.2.1
            (by decide) (by decide) ha⟩
      · exact ha.elim) avoid
  have rspA : stackPtr a = stackPtr initial - 416 := call.writes.1.trans pushed
  have outputA : a.regValue .rdi = stackPtr initial - 336 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans outputU
  have inputA : a.regValue .rsi = initial.regValue .rsi :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans inputU
  have boundInput : (registerRegion a .rsi 144).Bounded := by
    simpa only [registerRegion, inputA] using pre.inputBounded
  have allocatedInput : (registerRegion a .rsi 144).Allocated a.external := by
    intro address contains
    have contains' : (registerRegion initial .rsi 144).Contains address.toNat := by
      simpa only [registerRegion, inputA] using contains
    exact Option.isSome_iff_exists.mp (runningA.allocated address
      (Option.isSome_iff_exists.mpr (pre.inputAllocated address contains')))
  have inputApart : (registerRegion a .rsi 144).Disjoint (Stack.region initial 1264) := by
    have apart := pre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    change (registerRegion initial .rsi 144).Disjoint (Stack.region initial 1264) at apart
    simpa only [registerRegion, inputA] using apart
  have copyPre : CalleePre a boundary 0x10dd60 144 144 0 :=
    callee_pre_of_stack_output pre.stride pre.stack stackAvoid pre.outerBoundary
      runningA.machine runningA.directionFlag runningA.loaded runningA.allocated
      copyLayout (call.rip.trans target) rspA outputA (by
        rw [boundaryA]
        exact inProgram_of_textOffset 0xddb3 (by decide))
      boundInput allocatedInput inputApart
  have length : a.regValue .rdx = 144 :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans
      setupValues.2.2.2
  obtain ⟨t, result, bytes, copiedFrame⟩ := Common.Memory.memcpy_correct copyPre length (by decide)
  have runningT := runningA.of_callee result (by
    intro region member address contains
    exact ⟨Stack.region initial 1264, by simp,
      stack_layout_within pre.stack copyLayout rspA outputA region member address contains⟩)
  have inputSame := frame_agrees_of_disjoint runningA.frame
    (address := initial.regValue .rsi) (size := 144)
    (by have bound := pre.inputBounded; change (initial.regValue .rsi).toNat + 144 < 2^32 at bound; omega)
    (by
      intro region member
      have cases : region = registerRegion initial .rdi 176 ∨ region = Stack.region initial 1264 := by
        simpa using member
      rcases cases with rfl | rfl
      · exact pre.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
      · exact pre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide))
  have inputHmac : HmacAt a (initial.regValue .rsi) key message := hmac.of_copy inputSame
  have copied : HmacAt t (stackPtr initial - 336) key message := by
    apply inputHmac.of_copy
    intro i hi
    simpa only [inputA, outputA] using bytes i hi
  have preservedSaved : (Component.mem (stackPtr initial - 40) 48).Agrees a t :=
    frame_agrees_of_disjoint result.frame (by
      rw [show (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 from
        Common.CallFrame.stack_sub_toNat pre.stack (by decide : 40 ≤ 1264)]
      have bound := stack_bounds pre.stack
      omega)
      (stack_layout_disjoint pre.stack copyLayout rspA outputA (.inl (by decide)) (by decide))
  have callSaved : (Component.mem (stackPtr initial - 40) 48).Agrees u a := by
    intro i hi
    apply call.agrees.memory
    intro c hc cover
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · obtain ⟨j, hj, eq⟩ := cover
      apply OffsetsApart.ne (c₁ := -40) (len₁ := 48) (c₂ := -416) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
      simpa only [pushed, BitVec.sub_eq_add_neg] using eq
    · exact cover.elim
  have setupMemory := setup.agrees.external noMem
  refine ⟨t, runningT, ?_, ?_, ?_, copied, ?_, ?_, ?_, ?_⟩
  · exact result.rip.trans (by rw [boundaryA]; rfl)
  · have sp : stackPtr t = (returnBoundary a).rsp := result.rsp
    rw [boundaryA] at sp
    exact sp.trans rspU
  · exact (result.abi.1 .rbx (by simp)).trans
      ((call.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components])).trans bxU)
  · intro i hi
    rw [preservedSaved i hi, callSaved i hi, setupMemory, memoryS]
  · exact (result.abi.1 .rbp (by simp)).trans
      ((call.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components])).trans
        ((setup.agrees.read (n := 64) (r := 5) (by simp [setupEffect, Effect.components])).trans
          (saveFrame.read (n := 64) (r := 5) (by simp [savedComponents]))))
  · exact result.abi.2.2.1.trans
      ((call.agrees.mxcsr (by simp [callEffect, pushEffect_components])).trans
        ((setup.agrees.mxcsr (by simp [setupEffect, Effect.components])).trans
          (saveFrame.mxcsr (by simp [savedComponents]))))
  · exact result.abi.2.2.2.trans
      ((call.agrees.fcw (by simp [callEffect, pushEffect_components])).trans
        ((setup.agrees.fcw (by simp [setupEffect, Effect.components])).trans
          (saveFrame.fcw (by simp [savedComponents]))))

end Hkdf.Proofs.Standard.Finalize.Hmac
