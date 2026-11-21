import Sha2.Proofs.Common.SHA256.Finalize.Proof.CallGeometry

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem abi_read {s t : RamState} {r : BitVec 5} (abi : PreservesABI s t)
    (saved : r ∈ ([3,5,12,13,14,15] : List (BitVec 5))) :
    (.reg r : Operand 64).read t = (.reg r : Operand 64).read s := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl
  · exact abi.1 .rbx (by simp)
  · exact abi.1 .rbp (by simp)
  · exact abi.1 .r12 (by simp)
  · exact abi.1 .r13 (by simp)
  · exact abi.1 .r14 (by simp)
  · exact abi.1 .r15 (by simp)

theorem call [Bindings] (last : Bool) {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : HashAt L initial before s regions hash)
    (rip : s.RIP = if last then L.lastCall else L.firstCall)
    (rdi : s.regValue .rdi = L.hash (L.sp initial))
    (rsi : s.regValue .rsi = L.scratch (L.sp initial)) (count : s.regValue .rdx = 1)
    (bytes : (⟨(L.scratch (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, HashAt L initial before t regions
      (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk)) ∧
      t.RIP = (if last then L.exit else L.zero) ∧ PreservesABI s t := by
  let p := if last then L.lastCall else L.firstCall
  let disp := if last then L.lastDisp else L.firstDisp
  have inside : BlockInProgram p 5 := by
    cases last
    · exact ctx.code.inside .firstCall
    · exact ctx.code.inside .lastCall
  have pre : Blocks.CompressCall.Pre p (returnBoundary initial) hash chunk 1 s := by
    refine ⟨ctx.pushPre input.state input.rsp rip inside, inside 5 (by decide), ?_⟩
    intro u ready effect
    have frame := effect.agrees
    have slot : pushAddr s = L.sp initial-8 := by rw [pushAddr,input.rsp]
    simp only [callEffect,pushEffect_components,slot] at frame
    have rspU : stackPtr u = L.sp initial-8 := effect.writes.1.trans slot
    have rdiU : u.regValue .rdi = L.hash (L.sp initial) :=
      (frame.read (n := 64) (r := 7) (by simp)).trans rdi
    have rsiU : u.regValue .rsi = L.scratch (L.sp initial) :=
      (frame.read (n := 64) (r := 6) (by simp)).trans rsi
    have countU : u.regValue .rdx = 1 :=
      (frame.read (n := 64) (r := 2) (by simp)).trans count
    have machine := supportedMachine_of_ready_agrees input.state.machine ready effect.agrees
    have memory := effect.agrees.memoryWriteFrame (ctx.callWrites input.rsp _ _)
    have loaded : ProgramLoaded u := by
      intro a b fetch
      rw [memory a]
      · exact input.state.loaded a b fetch
      · intro region member contains
        exact ctx.footprint_avoids region member a contains ⟨b,fetch⟩
    have capacity := ctx.wf.capacity
    have bufferFits := ctx.wf.bufferFits
    have scratchFits := ctx.wf.scratchFits
    let layout : Wrapper.StackCallLayout reserve 64 32 336 :=
      ⟨L.frameBytes+8,L.frameBytes-L.variant.scratch,L.frameBytes-(L.variant.buffer.value+64),
        ctx.wf.aligned,by omega,by omega,by omega,by omega,by omega,by
          rcases ctx.wf.disjoint with h | h
          · right; omega
          · left; omega⟩
    have callee := Common.Machine.callee_pre_of_stack ctx.stride ctx.machine ctx.stack ctx.avoids
      ctx.returnAddress machine (effect.agrees.directionFlagClear (by simp [callEffect,pushEffect_components]) input.state.directionFlag)
      loaded (fun a ha => effect.agrees.grow a (input.state.allocated a ha)) layout effect.rip
      (by
        change stackPtr u = stackPtr initial-BitVec.ofNat 64 (L.frameBytes+8)
        rw [rspU]
        simp only [Layout.sp,BitVec.ofNat_add,BitVec.sub_sub,BitVec.ofNat_eq_ofNat])
      (by
        change u.regValue .rsi = stackPtr initial-BitVec.ofNat 64 (L.frameBytes-L.variant.scratch)
        rw [rsiU]
        exact L.address initial (by omega))
      (by
        change u.regValue .rdi = stackPtr initial-BitVec.ofNat 64 (L.frameBytes-(L.variant.buffer.value+64))
        rw [rdiU]
        simpa only [Layout.hash,Layout.buffer,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
          L.address initial (offset := L.variant.buffer.value+64) (by omega))
      (by
        have ret : (returnBoundary u).rip = p+5 := (callEffect_stack effect).1
        rw [ret]
        exact inside 5 (by decide))
    have kept (offset len : Nat) (apart : OffsetsApart (-8#64) 8 (BitVec.ofNat 64 offset) len)
        (bound : 8+len < 2^64) :
        ∀ i < len, u.external[L.sp initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          s.external[L.sp initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
      intro i hi
      apply frame.byte
      intro c hc covered
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨j,hj,he⟩ := covered
        apply apart.ne (L.sp initial) hj hi bound
        simpa only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat] using he.symm
      · exact covered.elim
    refine {
      toCalleePre := callee
      countRegister := countU
      inputBytes := ?_
      hashWords := ?_
    }
    · change (⟨(u.regValue .rsi).toNat,64⟩ : MemoryRegion).HasBytes u.external chunk
      rw [rsiU]
      refine ⟨bytes.1,?_⟩
      intro i
      have h := kept L.variant.scratch 64
        (by cases L.variant <;> unfold OffsetsApart <;> decide +kernel) (by decide) i.val
        (by have size : chunk.size=64 := bytes.1; omega)
      simpa only [Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using h.trans (by
        simpa only [Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using bytes.2 i)
    · rw [rdiU]
      apply Wrapper.hashState_of_bytes input.hashWords
      simpa only [Layout.hash,Layout.buffer,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
        kept (L.variant.buffer.value+64) 32
          (by cases L.variant <;> unfold OffsetsApart <;> decide +kernel) (by decide)
  obtain ⟨_,t,run,_,_,post⟩ := Blocks.CompressCall.run p disp (returnBoundary initial)
    (by cases last
        · exact ctx.flow.firstTarget
        · exact ctx.flow.lastTarget) ctx.outside
    (by intro u loaded; cases last
        · exact ctx.code.loaded .firstCall u loaded
        · exact ctx.code.loaded .lastCall u loaded)
    hash chunk 1 s (supportedMachine_readyToStep input.state.machine)
    (by cases last
        · exact ctx.code.loaded .firstCall s input.state.loaded
        · exact ctx.code.loaded .lastCall s input.state.loaded) pre
  obtain ⟨ripT,rspT,u,effect,result⟩ := post
  have frame := effect.agrees
  have rdiU : u.regValue .rdi = L.hash (L.sp initial) :=
    (frame.read (n := 64) (r := 7) (by simp [callEffect,pushEffect_components])).trans rdi
  have rspU : stackPtr u = L.sp initial-8 :=
    effect.writes.1.trans (by rw [pushAddr,input.rsp])
  have calleeWithin : ∀ region ∈ #v[registerRegion u .rdi 32,Stack.region u 336],
      ∀ a, region.Contains a → ∃ outer ∈ footprint L (L.sp initial),outer.Contains a := by
    intro region member a contains
    have cases : region=registerRegion u .rdi 32 ∨ region=Stack.region u 336 := by simpa using member
    rcases cases with rfl | rfl
    · refine ⟨⟨(L.hash (L.sp initial)).toNat,32⟩,by simp [footprint],?_⟩
      simpa only [registerRegion,rdiU] using contains
    · exact ⟨⟨(L.sp initial-344).toNat,344⟩,by simp [footprint],ctx.calleeStack_contains rspU (by decide) contains⟩
  have state := input.toPreserved.of_run_call_result ctx run effect
    (ctx.callWrites input.rsp _ _) result.toCalleeResult calleeWithin
  have abiCall : PreservesABI s u := by
    apply preservesABI_of_agrees frame input.state.directionFlag
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp [callEffect,pushEffect_components])
    · exact frame.read (n := 64) (r := 5) (by simp [callEffect,pushEffect_components])
    · exact frame.read (n := 64) (r := 12) (by simp [callEffect,pushEffect_components])
    · exact frame.read (n := 64) (r := 13) (by simp [callEffect,pushEffect_components])
    · exact frame.read (n := 64) (r := 14) (by simp [callEffect,pushEffect_components])
    · exact frame.read (n := 64) (r := 15) (by simp [callEffect,pushEffect_components])
    all_goals simp [callEffect,pushEffect_components]
  have abi : PreservesABI s t :=
    ⟨fun r hr => (result.abi.1 r hr).trans (abiCall.1 r hr),result.abi.2.1,
      result.abi.2.2.1.trans abiCall.2.2.1,result.abi.2.2.2.trans abiCall.2.2.2⟩
  refine ⟨t,⟨state,?_,?_⟩,?_,abi⟩
  · simpa only [rdiU,compressBlocks_single hash chunk bytes.1] using result.hashWords
  · intro notFirst
    exact (abi_read abi (by cases L.variant <;> decide)).trans (input.hashPointer notFirst)
  · cases last
    · exact ripT.trans ctx.flow.firstCall
    · exact ripT.trans ctx.flow.lastCall

end Sha2.Proofs.Common.SHA256.Finalize.Compress
