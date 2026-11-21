import Sha2.Proofs.Common.SHA256.Absorb.Proof.Calls

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem compress [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (site : CallSite) (member : site ∈ [l.fillCompressCall, l.bulkCall])
    {count : Nat} {chunk : ByteArray} {hash : Array UInt32}
    (rip : s.RIP = site.pc) (output : s.regValue .rdi = l.buffer (l.sp initial) + 64)
    (callee : ∀ u, ReadyToStep u →
      (callEffect (fun _ => 0x10b4e0) (site.pc + 5) s).Holds s u →
      CompressionPre u (returnBoundary initial) hash chunk count) :
    ∃ t, Preserved l initial before t regions ∧
      Blocks.CompressCall.Post site.pc (returnBoundary initial) hash chunk s t ∧
      HashStateAt t (l.buffer (l.sp initial) + 64) (compressBlocks hash chunk) ∧
      MemoryWriteFrame s t #v[(⟨(l.buffer (l.sp initial) + 64).toNat, 32⟩ : MemoryRegion),
        ⟨(l.sp initial - 344).toNat, 344⟩] := by
  obtain ⟨disp, encoding, target⟩ := ctx.targets.compressions site member
  have allCalls : site ∈ [l.smallCall, l.fillCall, l.fillCompressCall, l.bulkCall, l.tailCall] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl <;> simp
  have reload : ∀ u, ProgramLoaded u → CodeIn (codeRange site.pc (encodeCallRel32 disp)) u := by
    intro u loaded
    simpa only [encoding, CallEncoding.bytes] using ctx.code.calls site allCalls u loaded
  have push : PushPre site.pc 5 s := by
    simpa [encoding, CallEncoding.bytes, encodeCallRel32] using
      ctx.push_pre input.state input.rsp rip (ctx.code.calls site allCalls)
  have returnInside : InProgram (site.pc + 5) := by
    have returnPc : site.pc + 5 = site.pc + BitVec.ofNat 64 site.encoding.bytes.length := by
      rw [encoding]
      rfl
    rw [returnPc]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [ctx.flow.fillCompressReturn]
      exact ctx.code.inside .clearTail
    · rw [ctx.flow.bulkReturn]
      exact ctx.code.inside .bulkRestore
  obtain ⟨_, t, run, _, _, post⟩ := Blocks.CompressCall.run site.pc disp (returnBoundary initial)
    target ctx.outside reload hash chunk count s (supportedMachine_readyToStep input.state.machine)
    (reload s input.state.loaded) ⟨push, returnInside, callee⟩
  have fullPost := post
  obtain ⟨_, _, u, effect, result⟩ := fullPost
  have outputU : u.regValue .rdi = l.buffer (l.sp initial) + 64 :=
    (effect.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans output
  have rspU : stackPtr u = l.sp initial - 8 := by
    have pushed : stackPtr u = pushAddr s := effect.writes.1
    rw [pushed, pushAddr, input.rsp]
  have callWrites : WritesWithin (callEffect (fun _ => 0x10b4e0) (site.pc + 5) s).components
      #v[(⟨(l.buffer (l.sp initial) + 64).toNat, 32⟩ : MemoryRegion), ⟨(l.sp initial - 344).toNat, 344⟩] := by
    intro c member a covered
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · refine ⟨(⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion), by simp, ?_⟩
      apply call_slot_contains ctx.stack ctx.wf.capacity
      simpa only [pushAddr, input.rsp, Layout.sp] using covered
    · exact covered.elim
  have calleeWithin : ∀ region ∈ #v[registerRegion u .rdi 32, Stack.region u 336],
      ∀ a, region.Contains a → ∃ outer ∈
        #v[(⟨(l.buffer (l.sp initial) + 64).toNat, 32⟩ : MemoryRegion), ⟨(l.sp initial - 344).toNat, 344⟩],
        outer.Contains a := by
    intro region member a contains
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨(l.buffer (l.sp initial) + 64).toNat, 32⟩, by simp,
        by simpa only [registerRegion, outputU] using contains⟩
    · exact ⟨(⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion), by simp,
        callee_stack_contains ctx.stack ctx.wf.capacity rspU (by decide) contains⟩
  have within : ∀ region ∈
      #v[(⟨(l.buffer (l.sp initial) + 64).toNat, 32⟩ : MemoryRegion), ⟨(l.sp initial - 344).toNat, 344⟩],
      ∀ a, region.Contains a → ∃ outer ∈ footprint l (l.sp initial), outer.Contains a := by
    intro region member a contains
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨⟨(l.buffer (l.sp initial)).toNat, 104⟩, by simp [footprint], ?_⟩
      have bound : (l.buffer (l.sp initial)).toNat + 104 < 2^32 :=
        stack_frame_bounded ctx.stack (by have := ctx.wf.capacity; omega) ctx.wf.bufferFits
      have address : (l.buffer (l.sp initial) + 64).toNat = (l.buffer (l.sp initial)).toNat + 64 := by
        change ((l.buffer (l.sp initial)).toNat + 64) % 2^64 = _
        exact Nat.mod_eq_of_lt (by omega)
      change (l.buffer (l.sp initial) + 64).toNat ≤ a ∧
        a < (l.buffer (l.sp initial) + 64).toNat + 32 at contains
      rw [address] at contains
      change (l.buffer (l.sp initial)).toNat ≤ a ∧ a < (l.buffer (l.sp initial)).toNat + 104
      omega
    · exact ⟨_, by simp [footprint], contains⟩
  refine ⟨t, input.of_run_call_result ctx run effect ?_ result.toCalleeResult ?_, post,
    by simpa only [outputU] using result.hashWords,
    call_result_frame effect callWrites result.toCalleeResult calleeWithin⟩
  · intro c member a covered
    obtain ⟨r, hr, ha⟩ := callWrites c member a covered
    exact within r hr a.toNat ha
  · intro r member a contains
    obtain ⟨r', hr, ha⟩ := calleeWithin r member a contains
    exact within r' hr a ha

end Sha2.Proofs.Common.SHA256.Absorb
