import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Memory.Copy

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def copyLayout {destOffset count : Nat} (destStart : 272 ≤ destOffset)
    (destEnd : destOffset + count ≤ 336) : StackCallLayout 2264 0 count 0 :=
  ⟨544, 0, 536 - destOffset, by decide, by decide, by decide, by omega, by decide,
    by omega, .inr (by omega)⟩

theorem copyCall [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info input : ByteArray} {ptr : BitVec 64} {length destOffset count : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (buffered : Bool)
    (pc : s.RIP = (if buffered then 0x10f75d else 0x10f7db))
    (target : s.regValue .r12 = 0x10dd60)
    (dest : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 destOffset)
    (countArg : s.regValue .rdx = BitVec.ofNat 64 count)
    (destStart : 272 ≤ destOffset) (destEnd : destOffset + count ≤ 336)
    (sourceBound : (registerRegion s .rsi count).Bounded)
    (sourceApart : (registerRegion s .rsi count).Disjoint (Stack.region entry 2264))
    (bytes : (registerRegion s .rsi count).HasBytes s.external input) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = (if buffered then 0x10f760 else 0x10f7de) ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi count, ⟨(stackPtr s - 8).toNat, 8⟩] ∧
      (registerRegion s .rdi count).HasBytes t.external input := by
  let off : Nat := if buffered then 0xf75d else 0xf7db
  let p := Extracted.textAddress + BitVec.ofNat 64 off
  let layout := copyLayout destStart destEnd
  have stack := pre.call.stack
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have push : pushAddr s = stackPtr entry - 544 := by
    rw [pushAddr, sp, BitVec.sub_sub]
    rfl
  have localRun : Running s boundary #v[Stack.region entry 2264] s :=
    .initial saved.machine saved.loaded saved.directionFlag
  have instruction : CodeIn (codeRange p [0x41, 0xff, 0xd4]) s :=
    programText_slice (programLoaded_codeIn saved.loaded) off _ (by cases buffered <;> decide)
      (by cases buffered <;> decide +kernel)
  have step : StepEffect (X86Proofs.CallPre p 3 (fun u => u.regValue .r12))
      (codeRange p [0x41, 0xff, 0xd4]) (callEffect (fun u => u.regValue .r12) (p + 3)) :=
    call_r64_rex_effect_step p 0x41 0xd4 (by simp [RexPrefix]) rfl rfl
  have valid : X86Proofs.CallPre p 3 (fun u => u.regValue .r12) s := by
    refine ⟨⟨by cases buffered <;> exact pc, ?_, ?_⟩, by change (s.regValue .r12).toNat < 2 ^ 32; rw [target]; decide⟩
    · rw [push]
      exact stack_writable8 stack pre.call.stackAvoid saved.allocated (offset := 544) (by decide) (by decide)
    · rw [push]
      exact stack_codeApart stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp))
        (offset := 544) (codeOffset := off) (by decide) (by decide) (by cases buffered <;> decide)
  obtain ⟨c, runCall, ready, called⟩ := step.advances (boundary := boundary)
    (supportedMachine_readyToStep saved.machine) instruction valid (by
      change s.regValue .r12 ≠ boundary.rip
      rw [target]
      exact boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide)))
  have ret := call_boundary called
  have runC := localRun.of_agrees runCall ready called.agrees (by
    intro component member a covered
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · rw [push] at covered
      exact ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 (offset := 544)
        (by decide) (by decide) covered⟩
    · exact covered.elim) (by
      intro r hr a ha hp
      obtain rfl := Vector.mem_singleton.mp hr
      exact pre.call.stackAvoid a ha (.inl hp)) (by simp [callEffect, pushEffect_components])
  have rspC : stackPtr c = stackPtr entry - 544 := called.writes.1.trans push
  have outC : c.regValue .rdi = s.regValue .rdi :=
    called.agrees.read (r := 7) (n := 64) (by simp [callEffect, pushEffect_components])
  have outAddr : c.regValue .rdi = stackPtr entry - BitVec.ofNat 64 layout.outputOffset := by
    change _ = stackPtr entry - BitVec.ofNat 64 (536 - destOffset)
    rw [outC, dest, sp, ← BitVec.ofNat_sub_ofNat_of_le 536 destOffset (by omega) (by omega)]
    bv_omega
  have srcC : c.regValue .rsi = s.regValue .rsi :=
    called.agrees.read (r := 6) (n := 64) (by simp [callEffect, pushEffect_components])
  have sourceRegion : registerRegion c .rsi count = registerRegion s .rsi count := by
    simp only [registerRegion, srcC]
  have allocated : (registerRegion c .rsi count).Allocated c.external := by
    rw [sourceRegion]
    intro a ha
    change (s.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rsi).toNat + count at ha
    have n : input.size = count := bytes.1
    let i : Fin input.size := ⟨a.toNat - (s.regValue .rsi).toNat, by omega⟩
    have byte := bytes.2 i
    have addr : (registerRegion s .rsi count).start + i.val = a.toNat := by
      change (s.regValue .rsi).toNat + (a.toNat - (s.regValue .rsi).toNat) = a.toNat
      omega
    rw [addr, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    exact Option.isSome_iff_exists.mp (runC.allocated a (by simp only [byte, Option.isSome_some]))
  have callee : CalleePre c boundary 0x10dd60 count count 0 :=
    callee_pre_of_stack_output pre.call.stride stack pre.call.stackAvoid pre.call.outerBoundary
      runC.machine runC.directionFlag runC.loaded (fun a ha => runC.allocated a (saved.allocated a ha))
      layout (called.rip.trans target) rspC outAddr
      (by rw [ret]
          cases buffered
          · exact inProgram_of_textOffset 0xf7de (by decide)
          · exact inProgram_of_textOffset 0xf760 (by decide))
      (by rwa [sourceRegion]) allocated (by rwa [sourceRegion])
  have bytesC : (registerRegion c .rsi count).HasBytes c.external input := by
    apply frame_hasBytes (call_frame callee.stack called)
    · intro r hr
      obtain rfl := Vector.mem_singleton.mp hr
      exact callee.separation (0 : Fin 3) (2 : Fin 3) (by decide)
    · have bound : (registerRegion c .rsi count).start + count < 2^32 := callee.inputBounded
      change (registerRegion c .rsi count).start + count ≤ 2^64
      omega
    · rwa [sourceRegion]
  have countC : c.regValue .rdx = BitVec.ofNat 64 count :=
    (called.agrees.read (r := 2) (n := 64) (by simp [callEffect, pushEffect_components])).trans countArg
  obtain ⟨t, result, copied, _⟩ := Memory.memcpy_correct callee countC (by omega)
  obtain ⟨frame, abi⟩ := call_result callee called result saved.directionFlag
  have within := stack_layout_within stack layout rspC outAddr
  have runT := runC.of_callee result (by
    intro r hr a ha
    exact ⟨_, by simp, within r hr a ha⟩)
  obtain ⟨previous, prior⟩ := saved.execution
  obtain ⟨fuel, run⟩ := runT.execution
  have running : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t :=
    ⟨⟨previous + fuel, prior.trans run⟩, runT.machine, runT.loaded,
      fun a ha => runT.allocated a (saved.allocated a ha), runT.directionFlag,
      memoryWriteFrame_trans saved.frame (frame_mono runT.frame (by
        intro r hr a ha
        obtain rfl := Vector.mem_singleton.mp hr
        exact ⟨_, by simp, ha⟩))⟩
  have spT : stackPtr t = stackPtr s :=
    result.rsp.trans (congrArg ReturnBoundary.rsp ret)
  have keep (off size : Nat) (apart : off + count ≤ layout.outputOffset ∨
      layout.outputOffset + size ≤ off) (lo : off + 8 ≤ 544) (hi : size ≤ off + 8) :
      (Component.mem (stackPtr entry - BitVec.ofNat 64 off) size).Agrees s t := by
    apply frame_agrees_of_disjoint frame
    · rw [stack_sub_toNat stack (offset := off) (by omega)]
      have := stack_bounds stack
      omega
    · exact stack_layout_disjoint stack layout rspC outAddr apart lo
  have savedT := saved.of_agreement running spT (by
    change (Component.mem (stackPtr s + 488) 56).Agrees s t
    rw [show stackPtr s + 488 = stackPtr entry - 48 from by rw [sp]; bv_omega]
    exact keep 48 56 (.inl (by change 48 + count ≤ 536 - destOffset; omega)) (by decide) (by decide))
    (by
      change memLoad t.external (stackPtr t + 224) 64 = memLoad s.external (stackPtr s + 224) 64
      rw [spT, show stackPtr s + 224 = stackPtr entry - 312 from by rw [sp]; bv_omega]
      exact agrees_memLoad (keep 312 8 (.inr (by change 536 - destOffset + 8 ≤ 312; omega))
        (by decide) (by decide))) abi.2.2.1 abi.2.2.2
  refine ⟨t, savedT, ⟨fuel, run⟩, ?_, abi, ?_, ?_⟩
  · have ripT := result.rip.trans (congrArg ReturnBoundary.rip ret)
    cases buffered <;> exact ripT
  · have stackEq : Stack.region c 0 = ⟨(stackPtr s - 8).toNat, 8⟩ := by
      simp only [Stack.region, Nat.sub_zero, Nat.add_sub_cancel_left, Stack.returnAddressBytes]
      change (⟨(stackPtr c).toNat, 8⟩ : MemoryRegion) = _
      rw [show stackPtr c = stackPtr s - 8 from called.writes.1]
    simpa only [registerRegion, outC, stackEq] using frame
  · refine ⟨bytes.1, fun i => ?_⟩
    have size : input.size = count := bytes.1
    have copiedi := copied i.val (by have := i.isLt; omega)
    have sourcei := bytesC.2 i
    simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, outC] using copiedi.trans (by
        simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using sourcei)

end Hkdf.Proofs.NewExpand.Expand.Info
