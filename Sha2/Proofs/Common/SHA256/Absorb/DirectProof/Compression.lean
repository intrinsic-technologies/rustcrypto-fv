import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Calls

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.call_keeps_buffer (ctx : Context l initial regions reserve)
    {u : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (rsp : stackPtr s = l.sp initial) (effect : (callEffect target ret s).Holds s u) :
    ∀ i < 104, u.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
      s.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
  intro i hi
  apply effect.agrees.byte
  intro c member covered
  simp only [callEffect,pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · have written := ctx.callSlot_contains (by simpa only [pushAddr,rsp] using covered)
    have bufferBound : (l.buffer (l.sp initial)).toNat + 104 < 2^32 := ctx.buffer_bounded
    have address : (l.buffer (l.sp initial) + BitVec.ofNat 64 i).toNat =
        (l.buffer (l.sp initial)).toNat + i := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have high := written.2
    change _ < (l.sp initial - 344).toNat + 344 at high
    have callStack : (l.sp initial-344).toNat=(stackPtr initial).toNat-(l.frameBytes+344) := by
      simpa using ctx.below_toNat (by decide : 344≤344)
    rw [address,callStack,ctx.buffer_toNat] at high
    have bounds := stack_valid_bounds ctx.stack
    have capacity := ctx.wf.capacity
    omega
  · exact covered.elim

theorem compress (ctx : Context l initial regions reserve) {before : RamState}
    (input : Preserved l initial before s regions) {count : Nat} {chunk : ByteArray}
    {hash : Array UInt32} (rip : s.RIP = l.bulkCall.pc)
    (output : s.regValue .rdi = l.buffer (l.sp initial) + 64)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (bytes : (registerRegion s .rsi (64*count)).HasBytes s.external chunk)
    (bounded : (registerRegion s .rsi (64*count)).Bounded)
    (apart : (registerRegion s .rsi (64*count)).Disjoint (Stack.region initial reserve))
    (words : HashStateAt s (l.buffer (l.sp initial)+64) hash) :
    ∃ t, Preserved l initial before t regions ∧ t.RIP = l.pc .bulkTail ∧
      HashStateAt t (l.buffer (l.sp initial)+64) (compressBlocks hash chunk) ∧
      Blocks.CompressCall.Post l.bulkCall.pc (returnBoundary initial) hash chunk s t ∧
      MemoryWriteFrame s t #v[⟨(l.buffer (l.sp initial)+64).toNat,32⟩,
        ⟨(l.sp initial-344).toNat,344⟩] := by
  obtain ⟨disp,encoding,target⟩ := ctx.flow.compressionTarget
  have ret : l.bulkCall.pc + 5 = l.pc .bulkTail := by
    have h := ctx.flow.bulkReturn
    rw [encoding] at h
    exact h
  have reload : ∀ t, ProgramLoaded t → CodeIn (codeRange l.bulkCall.pc (encodeCallRel32 disp)) t := by
    intro t loaded
    have h := ctx.code.calls l.bulkCall (by simp) t loaded
    simpa only [encoding,CallEncoding.bytes] using h
  have inside : ∀ i < 5, InProgram (l.bulkCall.pc + BitVec.ofNat 64 i) := by
    intro i hi
    apply loaded_code_inProgram input.state.loaded reload
    exact mem_codeRange _ _ i (by simpa [encodeCallRel32] using hi)
  have pre : Blocks.CompressCall.Pre l.bulkCall.pc (returnBoundary initial) hash chunk count s := by
    refine ⟨ctx.pushPre input.state input.rsp rip inside, ret ▸ ctx.code.inside .bulkTail, ?_⟩
    intro u ready effect
    have fits := ctx.wf.bufferFits
    have capacity := ctx.wf.capacity
    have callee := callee_pre_after_call ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress
      input.state input.rsp (outputOffset := l.frameBytes-(l.bufferOffset+64))
      (frameOffset := l.frameBytes) (inputBytes := 64*count) (outputBytes := 32) (reserve := 336)
      (by
        rw [output]
        simpa only [Layout.buffer,Layout.sp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
          stack_frame_address initial (offset := l.bufferOffset+64) (by omega))
      ctx.wf.aligned (by omega) (by omega) (by omega) bounded
      (Common.Memory.hasBytes_allocated bytes) apart ready effect (ret ▸ ctx.code.inside .bulkTail)
    have sourceU : u.regValue .rsi = s.regValue .rsi := effect.agrees.read (n := 64) (r := 6)
      (by simp [callEffect,pushEffect_components])
    have outputU : u.regValue .rdi = l.buffer (l.sp initial)+64 :=
      (effect.agrees.read (n := 64) (r := 7) (by simp [callEffect,pushEffect_components])).trans output
    have sourceBytes : (registerRegion s .rsi (64*count)).HasBytes u.external chunk := by
      apply Common.Memory.hasBytes_of_frame bytes bounded
        (effect.agrees.memoryWriteFrame (ctx.callWrites input.rsp _ _))
      intro region member a ha hb
      exact apart a ha (ctx.footprint_subset region member a hb)
    refine ⟨callee,?_,?_,?_⟩
    · exact (effect.agrees.read (n := 64) (r := 2)
        (by simp [callEffect,pushEffect_components])).trans length
    · simpa only [registerRegion,sourceU] using sourceBytes
    · rw [outputU]
      apply Wrapper.hashState_of_bytes words
      intro i hi
      simpa only [BitVec.add_assoc,← BitVec.ofNat_add,BitVec.ofNat_eq_ofNat] using
        ctx.call_keeps_buffer input.rsp effect (64+i) (by omega)
  obtain ⟨_,t,run,_,_,post⟩ := Blocks.CompressCall.run l.bulkCall.pc disp (returnBoundary initial)
    target ctx.outside reload hash chunk count s (supportedMachine_readyToStep input.state.machine)
    (reload s input.state.loaded) pre
  have fullPost := post
  obtain ⟨ripT,_,u,effect,result⟩ := fullPost
  have outputU : u.regValue .rdi = l.buffer (l.sp initial)+64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [callEffect,pushEffect_components])).trans output
  have rspU : stackPtr u = l.sp initial-8 :=
    effect.writes.1.trans (by change stackPtr s-8 = _; rw [input.rsp])
  have preserved := input.of_run_call_result ctx.within run effect (ctx.callWrites input.rsp _ _)
    result.toCalleeResult (ctx.result_within rspU outputU (by decide : 64+32≤104) (by decide))
  refine ⟨t,preserved,ripT.trans ret,?_,post,?_⟩
  · simpa only [outputU] using result.hashWords
  · simpa only [registerRegion,outputU] using ctx.narrow_frame input.rsp effect result.toCalleeResult (by decide)

end Sha2.Proofs.Common.SHA256.Absorb.Direct
