import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Setup
import Hkdf.Proofs.Key
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Normalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine

private abbrev layout : StackCallLayout 1264 32 64 720 :=
  ⟨416, 192, 336, by decide, by decide, by decide, by decide, by decide,
    by decide, by right; decide⟩

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e0a9)
    (bytes : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes s.external digest) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e0c0 ∧
      (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes t.external digest ∧
      (MemoryRegion.mk (stackPtr initial - 336).toNat 64).HasBytes t.external
        (HMAC.keyBlock digest) := by
  obtain ⟨r, currentR, ipR, outR, inputR, lengthR, memoryR⟩ := Setup.run pre state rip
  have storedR : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes r.external digest := by
    rw [memoryR]; exact bytes
  have avoid : (Stack.region initial 1264).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) := pre.avoids _ (by simp)
  have pushed : pushAddr r = stackPtr initial - 416 := by
    change stackPtr r - 8 = _
    rw [currentR.rsp]; bv_omega
  have writable : MemWritable r (pushAddr r) 8 := by
    rw [pushed]
    exact CallFrame.stack_writable8 pre.stack avoid currentR.running.allocated
      (by decide) (by decide)
  have apart : RangeApart (pushAddr r) 8 0x10e0bb 5 := by
    rw [pushed]
    exact stack_codeApart pre.stack (fun a ha hp ↦ avoid a ha (.inl hp))
      (by decide) (by decide) (by decide : 0xe0bb + 5 ≤ 115149)
  have writes : WritesWithin
      (callEffect (fun _ ↦ (0x116320 : BitVec 64)) 0x10e0c0 r).components
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, pushed, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨Stack.region initial 1264, by simp,
        Hkdf.Proofs.Common.Machine.stackRegion_contains_sub pre.stack.2.2.1
          (by decide : 416 ≤ 1264) (by decide : 8 ≤ 416) ha⟩
    · exact ha.elim
  have step := call_rel32_effect_step 0x10e0bb 0x8260 (by decide)
  change StepEffect (PushPre 0x10e0bb 5)
    (codeRange 0x10e0bb (encodeCallRel32 0x8260))
    (callEffect (fun _ ↦ (0x116320 : BitVec 64)) 0x10e0c0) at step
  obtain ⟨c, currentC, effect, retC⟩ := currentR.running.call step
    (programText_slice (programLoaded_codeIn currentR.running.loaded) 0xe0bb
      (encodeCallRel32 0x8260) (by decide) (by decide +kernel))
    ⟨ipR, writable, apart⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x16320 (by decide)))
    writes (by
      intro region member a contains code
      exact pre.avoids region (by simpa using member) a contains (.inl code))
  have spC : stackPtr c = stackPtr initial - 416 := effect.writes.1.trans pushed
  have f : AgreesExcept [.reg 4, .mem (pushAddr r) 8, .rip] r c := by
    simpa only [callEffect, pushEffect_components] using effect.agrees
  have inputC : c.regValue .rsi = stackPtr initial - 192 :=
    (f.read (n := 64) (r := 6) (by simp)).trans inputR
  have outputC : c.regValue .rdi = stackPtr initial - 336 :=
    (f.read (n := 64) (r := 7) (by simp)).trans outR
  have lengthC : c.regValue .rdx = 32 :=
    (f.read (n := 64) (r := 2) (by simp)).trans lengthR
  have ret : returnBoundary c = ⟨0x10e0c0, stackPtr initial - 408⟩ := by
    simpa only [currentR.rsp] using retC
  have calleePre : CalleePre c boundary Key.entryAddress 32 64 720 :=
    callee_pre_of_stack pre.stride pre.stack avoid pre.outerBoundary
      currentC.machine currentC.directionFlag currentC.loaded currentC.allocated
      layout effect.rip spC inputC outputC (by
        rw [ret]; exact inProgram_of_textOffset 0xe0c0 (by decide))
  have digestSize : digest.size = 32 := bytes.1
  have preserved : (Component.mem (stackPtr initial - 192) 32).Agrees r c := by
    have same := Common.StreamPadding.Execution.call_local_agrees effect 216 32
      (by unfold OffsetsApart; decide +kernel) (by decide)
    simpa only [currentR.rsp,
      show stackPtr initial - 408 + BitVec.ofNat 64 216 = stackPtr initial - 192 by bv_omega]
      using same
  have storedC : (registerRegion c .rsi digest.size).HasBytes c.external digest := by
    rw [registerRegion, inputC, digestSize]
    refine ⟨storedR.1, fun i ↦ ?_⟩
    calc
      c.external[BitVec.ofNat 64 ((stackPtr initial - 192).toNat + i.val)]? =
          r.external[BitVec.ofNat 64 ((stackPtr initial - 192).toNat + i.val)]? := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact preserved i.val (by have := i.isLt; omega)
      _ = _ := storedR.2 i
  have ctx : Key.Context c boundary digest :=
    ⟨by simpa only [digestSize] using calleePre,
      by rw [lengthC, digestSize]; rfl, storedC⟩
  obtain ⟨t, result, normalized⟩ := Key.normalize_correct ctx
  have current := currentC.of_callee result (by
    intro region member a contains
    exact ⟨Stack.region initial 1264, by simp,
      stack_layout_within pre.stack layout spC outputC region member a contains⟩)
  obtain ⟨frame, abi⟩ := call_result calleePre effect result currentR.running.directionFlag
  have savedApart := stack_layout_disjoint pre.stack layout spC outputC
    (savedOffset := 40) (savedBytes := 48) (by left; decide) (by decide)
  have savedBound : (stackPtr initial - 40).toNat + 48 ≤ 2^64 := by
    change (stackPtr initial - BitVec.ofNat 64 40).toNat + 48 ≤ 2^64
    rw [CallFrame.stack_sub_toNat pre.stack (by decide : 40 ≤ 1264)]
    have bound := stack_bounds pre.stack
    omega
  have saved := frame_agrees_of_disjoint frame savedBound savedApart
  have digestApart := stack_layout_disjoint pre.stack layout spC outputC
    (savedOffset := 192) (savedBytes := 32) (by left; decide) (by decide)
  have digestBound : (stackPtr initial - 192).toNat + 32 ≤ 2^64 := by
    change (stackPtr initial - BitVec.ofNat 64 192).toNat + 32 ≤ 2^64
    rw [CallFrame.stack_sub_toNat pre.stack (by decide : 192 ≤ 1264)]
    have bound := stack_bounds pre.stack
    omega
  refine ⟨t, currentR.of_running current abi ?_ saved,
    ?_, frame_hasBytes frame digestApart digestBound storedR, ?_⟩
  · change t.regValue .rsp = _
    rw [result.rsp, ret, currentR.rsp]
  · rw [result.rip, ret]
  · simpa only [registerRegion, outputC] using normalized

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Normalize
