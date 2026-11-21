import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CallGeometry
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CopyCall
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.InputCall
import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Transport

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.result_within (ctx : Context l initial regions reserve)
    {u : RamState} {offset count calleeReserve : Nat}
    (rsp : stackPtr u = l.sp initial - 8)
    (output : u.regValue .rdi = l.buffer (l.sp initial) + BitVec.ofNat 64 offset)
    (bound : offset + count ≤ 104) (stackBound : calleeReserve ≤ 336) :
    ∀ region ∈ #v[registerRegion u .rdi count, Stack.region u calleeReserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint l (l.sp initial), outer.Contains a := by
  have bufferBound : (l.buffer (l.sp initial)).toNat + 104 < 2^32 := ctx.buffer_bounded
  have address : (l.buffer (l.sp initial) + BitVec.ofNat 64 offset).toNat =
      (l.buffer (l.sp initial)).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  intro region member a contains
  have cases : region = registerRegion u .rdi count ∨ region = Stack.region u calleeReserve :=
    by simpa using member
  rcases cases with rfl | rfl
  · refine ⟨⟨(l.buffer (l.sp initial)).toNat,104⟩, by simp [footprint], ?_⟩
    change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + count at contains
    rw [output, address] at contains
    change (l.buffer (l.sp initial)).toNat ≤ a ∧ a < (l.buffer (l.sp initial)).toNat + 104
    omega
  · exact ⟨⟨(l.sp initial - 344).toNat,344⟩, by simp [footprint],
      ctx.calleeStack_contains rsp stackBound contains⟩

theorem Context.narrow_frame (ctx : Context l initial regions reserve)
    {u t : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    {outputBytes calleeReserve : Nat} (rsp : stackPtr s = l.sp initial)
    (effect : (callEffect target ret s).Holds s u)
    (result : CalleeResult u t (returnBoundary initial) outputBytes calleeReserve)
    (stackBound : calleeReserve ≤ 336) :
    MemoryWriteFrame s t #v[registerRegion u .rdi outputBytes,
      ⟨(l.sp initial - 344).toNat,344⟩] := by
  have rspU : stackPtr u = l.sp initial - 8 :=
    effect.writes.1.trans (by change stackPtr s-8 = _; rw [rsp])
  apply call_result_frame effect ?_ result ?_
  · intro c member a covered
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · refine ⟨⟨(l.sp initial - 344).toNat,344⟩, by simp, ?_⟩
      apply ctx.callSlot_contains
      simpa only [pushAddr, rsp] using covered
    · exact covered.elim
  · intro region member a contains
    have cases : region = registerRegion u .rdi outputBytes ∨ region = Stack.region u calleeReserve :=
      by simpa using member
    rcases cases with rfl | rfl
    · exact ⟨registerRegion u .rdi outputBytes, by simp, contains⟩
    · exact ⟨⟨(l.sp initial - 344).toNat,344⟩, by simp,
        ctx.calleeStack_contains rspU stackBound contains⟩

theorem copy (ctx : Context l initial regions reserve) {before : RamState}
    (input : Preserved l initial before s regions) (site : CallSite)
    (member : site ∈ [l.smallCall,l.tailCall]) {count : Nat} {chunk : ByteArray}
    (rip : s.RIP = site.pc) (output : s.regValue .rdi = l.buffer (l.sp initial))
    (length : s.regValue .rdx = BitVec.ofNat 64 count) (small : count ≤ 63)
    (bytes : (registerRegion s .rsi count).HasBytes s.external chunk)
    (bounded : (registerRegion s .rsi count).Bounded)
    (apart : (registerRegion s .rsi count).Disjoint (Stack.region initial reserve))
    (returnInside : InProgram (site.pc + BitVec.ofNat 64 site.encoding.bytes.length)) :
    ∃ t, Preserved l initial before t regions ∧
      CopyCall.Post site (returnBoundary initial) count 0 s t ∧
      (⟨(l.buffer (l.sp initial)).toNat,count⟩ : MemoryRegion).HasBytes t.external chunk ∧
      MemoryWriteFrame s t #v[⟨(l.buffer (l.sp initial)).toNat,count⟩,
        ⟨(l.sp initial - 344).toNat,344⟩] := by
  have inside : ∀ i < site.encoding.bytes.length, InProgram (site.pc + BitVec.ofNat 64 i) := by
    intro i hi
    exact loaded_code_inProgram input.state.loaded (ctx.code.calls site (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl <;> simp)) (mem_codeRange _ _ i hi)
  have pre : CopyCall.Pre site (returnBoundary initial) count 0 s := by
    refine ⟨ctx.pushPre input.state input.rsp rip inside, ?_, returnInside, ?_⟩
    · obtain ⟨disp, encoding, pointer⟩ := ctx.flow.copyTargets site member
      unfold CopyCall.Target
      rw [encoding]
      refine ⟨by trivial, rfl, rfl, ?_, ?_⟩
      · change MemReadable s (site.pc + 6 + disp.signExtend 64) 8
        rw [pointer]
        exact (Wrapper.memcpy_pointer input.state.loaded).1
      · change (Operand.mem (site.pc + 6 + disp.signExtend 64) : Operand 64).read s = _
        rw [pointer]
        exact (Wrapper.memcpy_pointer input.state.loaded).2
    · intro u ready effect
      have fits := ctx.wf.bufferFits
      have capacity := ctx.wf.capacity
      refine ⟨callee_pre_after_call ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress
        input.state input.rsp (outputOffset := l.frameBytes-l.bufferOffset) ?_ ctx.wf.aligned (by omega) (by omega) (by omega)
        bounded (Common.Memory.hasBytes_allocated bytes) apart ready effect returnInside, ?_⟩
      · rw [output]
        exact stack_frame_address initial (by omega : l.bufferOffset ≤ l.frameBytes)
      · exact (effect.agrees.read (n := 64) (r := 2)
          (by simp [callEffect,pushEffect_components])).trans length
  obtain ⟨_,t,run,_,_,post⟩ := CopyCall.run site (returnBoundary initial) ctx.outside
    (ctx.code.calls site (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl <;> simp)) count 0 (by omega) s
    (supportedMachine_readyToStep input.state.machine)
    (ctx.code.calls site (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl <;> simp) s input.state.loaded) pre
  have fullPost := post
  obtain ⟨_,_,u,effect,result,copied⟩ := fullPost
  have outputU : u.regValue .rdi = l.buffer (l.sp initial) :=
    (effect.agrees.read (n := 64) (r := 7)
      (by simp [callEffect,pushEffect_components])).trans output
  have rspU : stackPtr u = l.sp initial - 8 :=
    effect.writes.1.trans (by change stackPtr s-8 = _; rw [input.rsp])
  have preserved := input.of_run_call_result ctx.within run effect
    (ctx.callWrites input.rsp _ _) result
    (ctx.result_within rspU (by simpa only [BitVec.add_zero] using outputU)
      (by omega : 0 + count ≤ 104) (by decide))
  have frame := ctx.narrow_frame input.rsp effect result (by decide)
  have sourceApart : RangeApart (s.regValue .rsi) count (pushAddr s) 8 := by
    intro i hi j hj same
    apply apart _ (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)
    rw [same]
    apply ctx.footprint_subset (⟨(l.sp initial-344).toNat,344⟩ : MemoryRegion) (by simp [footprint])
    apply ctx.callSlot_contains
    simpa only [pushAddr,input.rsp] using
      (show (Component.mem (pushAddr s) 8).Covers (pushAddr s+BitVec.ofNat 64 j) from ⟨j,hj,rfl⟩)
  have copiedBytes := CopyCall.Post.hasBytes post bytes sourceApart
  refine ⟨t,preserved,post,?_,?_⟩
  · simpa only [registerRegion,output] using copiedBytes
  · simpa only [registerRegion,outputU] using frame

end Sha2.Proofs.Common.SHA256.Absorb.Direct
