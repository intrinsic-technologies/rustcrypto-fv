import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive CompressionSite where
  | extra | inner | outer

def CompressionSite.offset : CompressionSite → Nat
  | .extra => 0xf9fd
  | .inner => 0xf3b8
  | .outer => 0xf4c6

def CompressionSite.pc (site : CompressionSite) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 site.offset

private def CompressionSite.delta : CompressionSite → BitVec 32
  | .extra => 0xffff9bbe
  | .inner => 0xffffa203
  | .outer => 0xffffa0f5

def CompressionSite.hashOffset : CompressionSite → Nat
  | .extra | .inner => 144
  | .outer => 184

private def CompressionSite.layout (site : CompressionSite) : StackCallLayout 2264 64 32 336 :=
  ⟨544, 520, 536 - site.hashOffset, by decide, by decide, by decide,
    by cases site <;> decide, by decide, by cases site <;> decide, by cases site <;> decide⟩

theorem compress [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info block : ByteArray} {ptr : BitVec 64} {length : Nat} {hash : Array UInt32}
    {n : Nat} {regions : Vector MemoryRegion n}
    (pre : ExpandPre entry boundary key info ptr length) (frame : Running entry boundary regions s)
    (sp : stackPtr s = stackPtr entry - 536)
    (site : CompressionSite) (rip : s.RIP = site.pc)
    (destination : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 site.hashOffset)
    (source : s.regValue .rsi = stackPtr s + 16) (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr s + 16).toNat, 64⟩ : MemoryRegion).HasBytes s.external block)
    (words : HashStateAt s (s.regValue .rdi) hash) :
    ∃ t, Running s boundary #v[Stack.region entry 2264] t ∧ t.RIP = site.pc + (5 : BitVec 64) ∧
      stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi 32, ⟨(stackPtr s).toNat - 344, 344⟩] ∧
      HashStateAt t (s.regValue .rdi)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  have stack := pre.call.stack
  have push : pushAddr s = stackPtr entry - 544 := by
    change stackPtr s - 8 = _
    rw [sp, BitVec.sub_sub]
    rfl
  have step := call_rel32_effect_step site.pc site.delta (by cases site <;> decide +kernel)
  have code := programText_slice (programLoaded_codeIn frame.loaded) site.offset
    (encodeCallRel32 site.delta) (by cases site <;> decide) (by cases site <;> decide +kernel)
  have target : branchTarget site.pc 5 (site.delta.signExtend 64) = 0x1095c0 := by
    cases site <;> decide +kernel
  have conditions : PushPre site.pc 5 s := by
    refine ⟨rip, ?_, ?_⟩
    · rw [push]
      exact stack_writable8 stack pre.call.stackAvoid frame.allocated (offset := 544) (by decide) (by decide)
    · rw [push]
      exact stack_codeApart stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp))
        (offset := 544) (codeOffset := site.offset) (by decide) (by decide) (by cases site <;> decide)
  have localRun : Running s boundary #v[Stack.region entry 2264] s :=
    .initial frame.machine frame.loaded frame.directionFlag
  obtain ⟨c, runC, called, ret⟩ := localRun.call step code conditions
    (by rw [target]; exact boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
    (by
      intro comp member a covered
      simp only [callEffect, pushEffect_components, push, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · exact ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 (offset := 544)
          (by decide) (by decide) covered⟩
      · exact covered.elim)
    (by
      intro r hr a ha hp
      obtain rfl := Vector.mem_singleton.mp hr
      exact pre.call.stackAvoid a ha (.inl hp))
  have spC : stackPtr c = stackPtr entry - 544 := called.writes.1.trans push
  have outC : c.regValue .rdi = s.regValue .rdi :=
    called.agrees.read (r := 7) (n := 64) (by simp [callEffect, pushEffect_components])
  have outAddr : c.regValue .rdi = stackPtr entry - BitVec.ofNat 64 site.layout.outputOffset := by
    rw [outC, destination, sp]
    cases site <;> simp only [CompressionSite.layout, CompressionSite.hashOffset, Nat.reduceSub, BitVec.ofNat_eq_ofNat] <;> bv_omega
  have inC : c.regValue .rsi = stackPtr s + 16 :=
    (called.agrees.read (r := 6) (n := 64) (by simp [callEffect, pushEffect_components])).trans source
  have inAddr : c.regValue .rsi = stackPtr entry - 520 := by rw [inC, sp]; bv_omega
  have callee := callee_pre_of_stack pre.call.stride stack pre.call.stackAvoid pre.call.outerBoundary
    runC.machine runC.directionFlag runC.loaded (fun a h => runC.allocated a (frame.allocated a h))
    site.layout (called.rip.trans target) spC inAddr outAddr (by
      rw [ret]
      cases site
      · exact inProgram_of_textOffset 0xfa02 (by decide)
      · exact inProgram_of_textOffset 0xf3bd (by decide)
      · exact inProgram_of_textOffset 0xf4cb (by decide))
  have compression : CompressionPre c boundary hash block 1 := by
    refine ⟨callee, ?_, called.agrees.read (r := 2) (n := 64)
      (by simp [callEffect, pushEffect_components]) |>.trans count, ?_, ?_⟩
    · rw [outAddr, stack_sub_toNat stack (by cases site <;> decide)]
      have aligned : (stackPtr entry).toNat % 16 = 8 := stack.2.2.2
      have bound := (stack_bounds stack).1
      cases site <;> simp only [CompressionSite.layout, CompressionSite.hashOffset, Nat.reduceSub] <;> omega
    · change (⟨(c.regValue .rsi).toNat,64⟩ : MemoryRegion).HasBytes _ _
      rw [inC]
      have same := StreamPadding.Execution.call_local_agrees called 16 64
        (by unfold OffsetsApart; decide +kernel) (by decide)
      refine ⟨bytes.1, fun i => ?_⟩
      have hi : i.val < 64 := by have := i.isLt; have h : block.size = 64 := bytes.1; omega
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq] using
        (same i.val hi).trans (by
          simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq] using bytes.2 i)
    · rw [outC]
      apply hashState_of_bytes words
      rw [destination]
      exact StreamPadding.Execution.call_local_agrees called site.hashOffset 32
        (by cases site <;> unfold OffsetsApart <;> decide +kernel) (by decide)
  obtain ⟨t, result⟩ := compression_correct compression
  have runT := runC.of_callee result.toCalleeResult (by
    intro r hr a ha
    exact ⟨_, by simp, stack_layout_within stack site.layout spC outAddr r hr a ha⟩)
  obtain ⟨writes, abi⟩ := call_result callee called result.toCalleeResult frame.directionFlag
  have stackEq : Stack.region c 336 = ⟨(stackPtr s).toNat - 344, 344⟩ := by
    change (⟨(stackPtr c).toNat - 336, (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 336)⟩ : MemoryRegion) = _
    have cNat : (stackPtr c).toNat = (stackPtr entry).toNat - 544 :=
      (congrArg BitVec.toNat spC).trans (stack_sub_toNat stack (offset := 544) (by decide))
    have sNat : (stackPtr s).toNat = (stackPtr entry).toNat - 536 :=
      (congrArg BitVec.toNat sp).trans (stack_sub_toNat stack (offset := 536) (by decide))
    rw [cNat, sNat]
    have bound := (stack_bounds stack).1
    rw [MemoryRegion.mk.injEq]
    constructor <;> omega
  refine ⟨t, runT, result.rip.trans (congrArg ReturnBoundary.rip ret),
    result.rsp.trans (congrArg ReturnBoundary.rsp ret), abi, ?_, ?_⟩
  · simpa only [registerRegion, outC, stackEq] using writes
  · simpa only [outC, compressBlocks_single hash block bytes.1] using result.hashWords

end Hkdf.Proofs.NewExpand.Expand.Finalize
