import Hkdf.Proofs.Key.Entry.SaveState
import Hkdf.Proofs.Key.Entry.ZeroBytes
import Hkdf.Proofs.Key.Entry.Branch
import Hkdf.Proofs.Common.CallFrame

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine (supportedMachine_readyToStep)

theorem block_add (initial : RamState) {slot : Nat} (h : slot ≤ 376) :
    blockAddress initial + BitVec.ofNat 64 slot =
      stackPtr initial - BitVec.ofNat 64 (376-slot) := by
  unfold blockAddress
  apply BitVec.eq_sub_iff_add_eq.mpr
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show slot + (376 - slot) = 376 by omega]
  exact BitVec.sub_add_cancel _ _

theorem prepare [Bindings] {initial : RamState} {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) :
    ∃ s, Prepared initial boundary s ∧
      ((key.size ≤ 64 ∧ s.RIP = 0x116380) ∨ (64 < key.size ∧ s.RIP = 0x11638e)) := by
  obtain ⟨s,state,rip,sp,output,input,length⟩ := save ctx
  have sp' : rspOf s = blockAddress initial := sp
  have pre : Zero.Pre s := by
    refine ⟨rip, ?_, ?_⟩
    · intro slot hs
      have bound : slot ≤ 56 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have align : (376-slot) % 8 = 0 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [sp',block_add initial (by omega)]
      exact stack_writable8 ctx state (by omega) align
    · intro slot hs ip len hlo hhi
      have bound : slot ≤ 56 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [sp',block_add initial (by omega)]
      have code := stack_codeApart ctx (offset := 376-slot) (len := 8)
        (codeOffset := ip-0x100000) (codeLen := len) (by omega) (by omega) (by omega)
      have ipEq : Extracted.textAddress + BitVec.ofNat 64 (ip-0x100000) =
          BitVec.ofNat 64 ip := by
        change BitVec.ofNat 64 0x100000 + _ = _
        rw [← BitVec.ofNat_add]
        exact congrArg (BitVec.ofNat 64) (show 0x100000 + (ip - 0x100000) = ip by omega)
      rw [ipEq] at code
      exact code
  obtain ⟨fuel,u,run,ready,_,effect⟩ := Zero.run boundary (by
    intro ip hlo hhi
    have ipEq : (BitVec.ofNat 64 ip) = Extracted.textAddress +
        BitVec.ofNat 64 (ip-0x100000) := by
      change _ = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (show ip = 0x100000 + (ip - 0x100000) by omega)
    rw [ipEq]
    exact boundary_ne_program ctx.outerBoundary
      (inProgram_of_textOffset (ip-0x100000) (by omega))) s
    (supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) 0x16333 Zero.bytes
      (by decide +kernel) (by decide +kernel)) pre
  have frame : AgreesExcept
      [.mem (rspOf s+56) 8,.mem (rspOf s+48) 8,.mem (rspOf s+40) 8,
        .mem (rspOf s+32) 8,.mem (rspOf s+24) 8,.mem (rspOf s+16) 8,
        .mem (rspOf s+8) 8,.mem (rspOf s) 8,.rip] s u := by
    simpa only [Zero.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      Nat.reduceDiv] using effect.agrees
  have localWrites : LocalWrites initial
      [.mem (rspOf s+56) 8,.mem (rspOf s+48) 8,.mem (rspOf s+40) 8,
        .mem (rspOf s+32) 8,.mem (rspOf s+24) 8,.mem (rspOf s+16) 8,
        .mem (rspOf s+8) 8,.mem (rspOf s) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [sp'] at ha
    · have address : blockAddress initial + (56 : BitVec 64) =
          stackPtr initial - (320 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 56) (by decide)
      rw [address] at ha
      exact local_memory (offset := 320) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (48 : BitVec 64) =
          stackPtr initial - (328 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 48) (by decide)
      rw [address] at ha
      exact local_memory (offset := 328) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (40 : BitVec 64) =
          stackPtr initial - (336 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 40) (by decide)
      rw [address] at ha
      exact local_memory (offset := 336) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (32 : BitVec 64) =
          stackPtr initial - (344 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 32) (by decide)
      rw [address] at ha
      exact local_memory (offset := 344) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (24 : BitVec 64) =
          stackPtr initial - (352 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 24) (by decide)
      rw [address] at ha
      exact local_memory (offset := 352) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (16 : BitVec 64) =
          stackPtr initial - (360 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 16) (by decide)
      rw [address] at ha
      exact local_memory (offset := 360) (len := 8) (by decide) (by decide) a ha
    · have address : blockAddress initial + (8 : BitVec 64) =
          stackPtr initial - (368 : BitVec 64) := by
        simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
          block_add initial (slot := 8) (by decide)
      rw [address] at ha
      exact local_memory (offset := 368) (len := 8) (by decide) (by decide) a ha
    · change (Component.mem (stackPtr initial - 376) 8).Covers a at ha
      exact local_memory (offset := 376) (len := 8) (by decide) (by decide) a ha
  have current : State initial boundary u := by
    have running := state.toRunning.of_agrees run ready frame (localWrites.within ctx) (by
      intro region member address contains inside
      exact ctx.avoids region (by simpa [writeRegions] using member)
        address contains (.inl inside)) (by simp)
    have saved := state.saved.of_agrees (fun i hi ↦
      frame.byte (fun c hc ↦ localWrites.saved c hc _ ⟨i, hi, rfl⟩))
    exact ⟨running, saved, (frame.read (n := 64) (r := 5) (by simp)).trans state.rbp,
      (frame.mxcsr (by simp)).trans state.mxcsr, (frame.fcw (by simp)).trans state.fcw⟩
  have prepared : Prepared initial boundary u := by
    refine ⟨current, (frame.read (n := 64) (r := 4) (by simp)).trans sp,
      (frame.read (n := 64) (r := 3) (by simp)).trans output,
      (frame.read (n := 64) (r := 6) (by simp)).trans input,
      (frame.read (n := 64) (r := 2) (by simp)).trans length, ?_⟩
    rw [← sp']
    apply Zero.hasBytes effect
    rw [sp']
    exact stack_readable ctx current (by decide) (by decide)
  obtain ⟨t,branchRun,readyT,target,branchFrame⟩ := Branch.run
    (supportedMachine_readyToStep current.machine)
    (programText_slice (programLoaded_codeIn current.loaded) 0x1637a Branch.bytes
      (by decide +kernel) (by decide +kernel)) effect.rip
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1637e (by decide)))
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16380 (by decide)))
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1638e (by decide)))
  have final : State initial boundary t := by
    have running := current.toRunning.of_agrees branchRun readyT branchFrame
      (by simp [WritesWithin, Component.Covers]) (by
        intro region member address contains inside
        exact ctx.avoids region (by simpa [writeRegions] using member)
          address contains (.inl inside)) (by simp)
    have saved := current.saved.of_agrees (fun i hi ↦
      branchFrame.byte (by simp [Component.Covers]))
    exact ⟨running, saved, (branchFrame.read (n := 64) (r := 5) (by simp)).trans current.rbp,
      (branchFrame.mxcsr (by simp)).trans current.mxcsr,
      (branchFrame.fcw (by simp)).trans current.fcw⟩
  have finalPrepared : Prepared initial boundary t := by
    refine ⟨final,(branchFrame.read (n := 64) (r := 4) (by simp)).trans prepared.rsp,
      (branchFrame.read (n := 64) (r := 3) (by simp)).trans prepared.outputPointer,
      (branchFrame.read (n := 64) (r := 6) (by simp)).trans prepared.inputPointer,
      (branchFrame.read (n := 64) (r := 2) (by simp)).trans prepared.inputLength, ?_⟩
    rw [branchFrame.external (by simp [Component.Covers])]
    exact prepared.zeroBlock
  have size : (u.regValue .rdx).toNat = key.size := by
    rw [prepared.inputLength]
    exact ctx.length
  rw [size] at target
  refine ⟨t,finalPrepared,?_⟩
  by_cases h : key.size ≤ 64
  · exact .inl ⟨h,by simpa only [h,↓reduceIte] using target⟩
  · exact .inr ⟨by omega,by simpa only [h,↓reduceIte] using target⟩

end Hkdf.Proofs.Key.Entry
