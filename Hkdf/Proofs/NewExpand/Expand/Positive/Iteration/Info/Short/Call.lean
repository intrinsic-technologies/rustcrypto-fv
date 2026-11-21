import Hkdf.Proofs.NewExpand.Calls
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Memory.Copy

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info.Short

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private abbrev copyLayout {previous size : Nat} (short : previous + size < 64) :
    StackCallLayout 2264 0 size 0 :=
  ⟨544, 0, 264 - previous, by decide, by decide, by decide, by omega, by decide,
    by omega, .inr (by omega)⟩

theorem copyCall [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length previousSize : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (running : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] s)
    (sp : stackPtr s = stackPtr entry - 536) (positive : 0 < length) (allowed : length ≤ 8160)
    (pc : s.RIP = 0x10f701) (target : s.regValue .r12 = 0x10dd60)
    (dest : s.regValue .rdi = stackPtr s + 272 + BitVec.ofNat 64 previousSize)
    (source : s.regValue .rsi = ptr) (count : s.regValue .rdx = BitVec.ofNat 64 info.size)
    (short : previousSize + info.size < 64) :
    ∃ t, (∃ fuel, Advances boundary fuel s t) ∧
      Running entry boundary
        #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t ∧
      t.RIP = 0x10f704 ∧ stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      (⟨(stackPtr s + 272 + BitVec.ofNat 64 previousSize).toNat, info.size⟩ : MemoryRegion).HasBytes
        t.external info ∧
      MemoryWriteFrame s t #v[⟨(stackPtr s + 272 + BitVec.ofNat 64 previousSize).toNat, info.size⟩,
        ⟨(stackPtr s - 8).toNat, 8⟩] := by
  have stack := pre.call.stack
  have push : pushAddr s = stackPtr entry - 544 := by rw [pushAddr, sp, BitVec.sub_sub]; rfl
  let callTarget := fun u : RamState ↦ u.regValue .r12
  have step : StepEffect (X86Proofs.CallPre 0x10f701 3 callTarget)
      (codeRange 0x10f701 [0x41, 0xff, 0xd4]) (callEffect callTarget 0x10f704) :=
    call_r64_rex_effect_step 0x10f701 0x41 0xd4 (by simp [RexPrefix]) rfl rfl
  have ins := programText_slice (programLoaded_codeIn running.loaded) 0xf701 [0x41, 0xff, 0xd4]
    (by decide) (by decide +kernel)
  have hp : X86Proofs.CallPre 0x10f701 3 callTarget s := by
    refine ⟨⟨pc, ?_, ?_⟩, ?_⟩
    · rw [push]
      exact stack_writable8 stack pre.call.stackAvoid running.allocated (offset := 544) (by decide) (by decide)
    · rw [push]
      exact stack_codeApart stack (fun a ha h ↦ pre.call.stackAvoid a ha (.inl h))
        (offset := 544) (codeOffset := 0xf701) (by decide) (by decide) (by decide)
    · change (s.regValue .r12).toNat < 2^32
      rw [target]
      decide
  obtain ⟨c, advance, ready, call⟩ := step.advances (supportedMachine_readyToStep running.machine)
    ins hp (by change s.regValue .r12 ≠ _; rw [target]
               exact boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide)))
  have sep := pre.separation positive allowed
  have runningC := running.of_agrees advance ready call.agrees (by
    intro comp hm a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ha.elim
    · rw [push] at ha
      exact ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 (offset := 544) (by decide) (by decide) ha⟩
    · exact ha.elim) (by
    intro r hr a ha h
    simp only [writtenLength, allowed, ↓reduceIte] at hr
    exact (sep.2 r hr).2 a ha (.inl h)) (by simp [callEffect, pushEffect_components])
  have spC : stackPtr c = stackPtr entry - 544 := call.writes.1.trans push
  have sourceC : c.regValue .rsi = ptr :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  have destC : c.regValue .rdi = stackPtr s + 272 + BitVec.ofNat 64 previousSize :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans dest
  have countC : c.regValue .rdx = BitVec.ofNat 64 info.size :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans count
  have output : c.regValue .rdi = stackPtr entry - BitVec.ofNat 64 (264 - previousSize) := by
    rw [destC, sp, ← BitVec.ofNat_sub_ofNat_of_le 264 previousSize (by omega) (by omega)]
    bv_omega
  let input : MemoryRegion := ⟨ptr.toNat, info.size⟩
  have sourceRegion : registerRegion c .rsi info.size = input := by simp only [registerRegion, sourceC, input]
  have bytes := pre.infoBytes positive allowed
  have apart (r : MemoryRegion) (hr : r ∈ #v[registerRegion entry .rcx (writtenLength length),
      Stack.region entry 2264]) : input.Disjoint r := by
    simp only [writtenLength, allowed, ↓reduceIte] at hr
    exact (sep.2 r hr).1 input (by simp [input])
  have stored : input.HasBytes c.external info := frame_hasBytes runningC.frame apart
    (by have b : ptr.toNat + info.size < 2^32 := bytes.1
        change ptr.toNat + info.size ≤ 2^64
        omega) bytes.2
  have ret := call_boundary call
  have callee : CalleePre c boundary 0x10dd60 info.size info.size 0 := by
    apply callee_pre_of_stack_output pre.call.stride stack pre.call.stackAvoid pre.call.outerBoundary
      runningC.machine runningC.directionFlag runningC.loaded runningC.allocated (copyLayout short)
      (call.rip.trans target) spC output (by rw [ret]; exact inProgram_of_textOffset 0xf704 (by decide))
    · rw [sourceRegion]
      exact bytes.1
    · rw [sourceRegion]
      intro a ha
      change ptr.toNat ≤ a.toNat ∧ a.toNat < ptr.toNat + info.size at ha
      have byte := stored.2 ⟨a.toNat - ptr.toNat, by omega⟩
      change c.external[BitVec.ofNat 64 (ptr.toNat + (a.toNat - ptr.toNat))]? = _ at byte
      rw [Nat.add_sub_of_le ha.1, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact ⟨_, byte⟩
    · rw [sourceRegion]
      exact apart _ (by simp)
  obtain ⟨t, result, copied, _⟩ := Memory.memcpy_correct callee countC (by omega)
  obtain ⟨fuel, run⟩ := result.execution
  obtain ⟨frame, abi⟩ := call_result callee call result running.directionFlag
  have runningT := runningC.of_callee result (by
    intro r hr a ha
    exact ⟨_, by simp, stack_layout_within stack (copyLayout short) spC output r hr a ha⟩)
  have pushRegion : Stack.region c 0 = ⟨(stackPtr s - 8).toNat, 8⟩ := by
    have : stackPtr c = stackPtr s - 8 := call.writes.1
    change (⟨(stackPtr c).toNat - 0, (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 0)⟩ : MemoryRegion) = _
    simp only [Nat.sub_zero, Nat.add_sub_cancel_left, this]
  refine ⟨t, ⟨1 + fuel, advance.trans run⟩, runningT, result.rip.trans (congrArg ReturnBoundary.rip ret),
    result.rsp.trans (congrArg ReturnBoundary.rsp ret), abi, ⟨rfl, ?_⟩, ?_⟩
  · intro i
    have byte := copied i.val i.isLt
    rw [sourceC, destC] at byte
    simpa only [input, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte.trans (by simpa only [input, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using stored.2 i)
  · simpa only [registerRegion, destC, pushRegion] using frame

end Hkdf.Proofs.NewExpand.Expand.Info.Short
