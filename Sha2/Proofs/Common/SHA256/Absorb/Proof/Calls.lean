import Sha2.Proofs.Common.SHA256.Absorb.Proof.CallFrame
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CopyCall
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.InputCall
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.InputBytes
import Sha2.Proofs.Wrapper.Call

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem CallTargets.copy_target {l : Layout} {site : CallSite} {s : RamState}
    (targets : CallTargets l) (loaded : ProgramLoaded s)
    (member : site ∈ [l.smallCall, l.fillCall, l.tailCall])
    (register : ∀ r, site.encoding = .register r → Blocks.readReg s r = 0x10dd60) :
    CopyCall.Target site s := by
  have target := targets.copies site member
  cases encoding : site.encoding with
  | relative disp =>
    simpa only [CopyCall.Target, encoding] using target
  | memory am =>
    rw [encoding] at target
    obtain ⟨disp, rfl, pointer⟩ := target
    rw [CopyCall.Target, encoding]
    refine ⟨by trivial, rfl, rfl, ?_, ?_⟩
    · change MemReadable s (site.pc + 6 + disp.signExtend 64) 8
      rw [pointer]
      exact (Wrapper.memcpy_pointer loaded).1
    · change (Operand.mem (site.pc + 6 + disp.signExtend 64) : Operand 64).read s = _
      rw [pointer]
      exact (Wrapper.memcpy_pointer loaded).2
  | register r =>
    simpa only [CopyCall.Target, encoding, Blocks.readReg] using register r encoding

theorem Context.push_pre [Bindings] {l : Layout} {initial s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (state : ExecutionState initial s regions)
    (rsp : stackPtr s = l.sp initial) {site : CallSite} (rip : s.RIP = site.pc)
    (loaded : ∀ t, ProgramLoaded t → CodeIn (codeRange site.pc site.encoding.bytes) t) :
    PushPre site.pc site.encoding.bytes.length s := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (l.frameBytes + 8) := by
    rw [pushAddr, rsp]
    change stackPtr initial - BitVec.ofNat 64 l.frameBytes - 8 = _
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  refine ⟨rip, ?_, ?_⟩
  · rw [address]
    exact Common.Encoding.Serialize.writable_of_grow
      (stack_valid_sub_writable ctx.stack (fun a ha hp => ctx.avoids a ha (.inr hp))
        (by have := ctx.wf.capacity; omega) (by omega) (by decide)) state.allocated
  · intro i hi j hj equal
    apply ctx.avoids (pushAddr s + BitVec.ofNat 64 i)
    · apply stackRegion_contains_sub ctx.stack.2.2.1
        (by have := ctx.wf.capacity; omega : l.frameBytes + 8 ≤ reserve)
        (by omega : 8 ≤ l.frameBytes + 8)
      rw [← address]
      exact ⟨i, hi, rfl⟩
    · exact Or.inl (equal ▸ Direct.loaded_code_inProgram state.loaded loaded
        (mem_codeRange _ _ j hj))

theorem copy [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (site : CallSite) (member : site ∈ [l.smallCall, l.fillCall, l.tailCall])
    {offset count : Nat} {chunk : ByteArray}
    (rip : s.RIP = site.pc)
    (output : s.regValue .rdi = l.buffer (l.sp initial) + BitVec.ofNat 64 offset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count) (bound : offset + count ≤ 64)
    (bytes : (registerRegion s .rsi count).HasBytes s.external chunk)
    (bounded : (registerRegion s .rsi count).Bounded)
    (apart : (registerRegion s .rsi count).Disjoint (Stack.region initial reserve))
    (targetRegister : ∀ r, site.encoding = .register r → Blocks.readReg s r = 0x10dd60)
    (returnInside : InProgram (site.pc + BitVec.ofNat 64 site.encoding.bytes.length)) :
    ∃ t, Preserved l initial before t regions ∧
      CopyCall.Post site (returnBoundary initial) count 0 s t ∧
      (registerRegion s .rdi count).HasBytes t.external chunk ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi count,
        ⟨(l.sp initial - 344).toNat, 344⟩] := by
  have allCalls : site ∈ [l.smallCall, l.fillCall, l.fillCompressCall, l.bulkCall, l.tailCall] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  have pre : CopyCall.Pre site (returnBoundary initial) count 0 s := by
    refine ⟨ctx.push_pre input.state input.rsp rip (ctx.code.calls site allCalls),
      ctx.targets.copy_target input.state.loaded member targetRegister, returnInside, ?_⟩
    intro u ready effect
    have fits := ctx.wf.bufferFits
    have capacity := ctx.wf.capacity
    refine ⟨callee_pre_after_call (outputOffset := l.frameBytes - (l.bufferOffset + offset))
      ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress
      input.state input.rsp ?_ ctx.wf.aligned (by omega) (by omega) (by omega)
      bounded (Common.Memory.hasBytes_allocated bytes) apart ready effect returnInside, ?_⟩
    · rw [output]
      simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using
        (stack_frame_address initial (by omega : l.bufferOffset + offset ≤ l.frameBytes))
    · exact (effect.agrees.read (n := 64) (r := 2)
        (by simp [callEffect, pushEffect_components])).trans length
  obtain ⟨fuel, t, run, _, _, post⟩ := CopyCall.run site (returnBoundary initial) ctx.outside
    (ctx.code.calls site allCalls) count 0 (by omega) s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.calls site allCalls s input.state.loaded) pre
  have postCopy := post
  obtain ⟨_, _, u, effect, result, _⟩ := postCopy
  have rspU : stackPtr u = l.sp initial - 8 := by
    have push : stackPtr u = pushAddr s := effect.writes.1
    rw [push, pushAddr, input.rsp]
  have outputU : u.regValue .rdi = s.regValue .rdi := effect.agrees.read (n := 64) (r := 7)
    (by simp [callEffect, pushEffect_components])
  have slot {a : BitVec 64} (covered : (Component.mem (pushAddr s) 8).Covers a) :
      (⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a.toNat := by
    apply call_slot_contains ctx.stack ctx.wf.capacity
    simpa only [pushAddr, input.rsp, Layout.sp] using covered
  have stack {a : Nat} (contains : (Stack.region u 0).Contains a) :
      (⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a :=
    callee_stack_contains ctx.stack ctx.wf.capacity rspU (by decide) contains
  have callWrites : WritesWithin (callEffect (fun _ => 0x10dd60)
      (site.pc + BitVec.ofNat 64 site.encoding.bytes.length) s).components
      #v[registerRegion s .rdi count, ⟨(l.sp initial - 344).toNat, 344⟩] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨_, by simp, slot ha⟩
    · exact ha.elim
  have calleeWithin : ∀ region ∈ #v[registerRegion u .rdi count, Stack.region u 0],
      ∀ a, region.Contains a → ∃ outer ∈
        #v[registerRegion s .rdi count, ⟨(l.sp initial - 344).toNat, 344⟩], outer.Contains a := by
    intro region hr a ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨registerRegion s .rdi count, by simp, by simpa only [registerRegion, outputU] using ha⟩
    · exact ⟨_, by simp, stack ha⟩
  have within : ∀ region ∈ #v[registerRegion s .rdi count,
      ⟨(l.sp initial - 344).toNat, 344⟩], ∀ a, region.Contains a →
      ∃ outer ∈ footprint l (l.sp initial), outer.Contains a := by
    intro region hr a ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨⟨(l.buffer (l.sp initial)).toNat, 104⟩, by simp [footprint], ?_⟩
      have bb : (l.buffer (l.sp initial)).toNat + 104 < 2^32 :=
        stack_frame_bounded ctx.stack (by have := ctx.wf.capacity; omega) ctx.wf.bufferFits
      have address : (s.regValue .rdi).toNat = (l.buffer (l.sp initial)).toNat + offset := by
        rw [output, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + count at ha
      rw [address] at ha
      change (l.buffer (l.sp initial)).toNat ≤ a ∧ a < (l.buffer (l.sp initial)).toNat + 104
      omega
    · exact ⟨_, by simp [footprint], ha⟩
  have preserved : Preserved l initial before t regions :=
    input.of_run_call_result ctx run effect
      (fun c hc a ha => by obtain ⟨r, hr, h⟩ := callWrites c hc a ha; exact within r hr _ h)
      result (fun r hr a ha => by
        obtain ⟨r', hr', h⟩ := calleeWithin r hr a ha
        exact within r' hr' _ h)
  refine ⟨t, preserved, post, post.hasBytes bytes ?_,
    call_result_frame effect callWrites result calleeWithin⟩
  intro i hi j hj same
  apply apart (s.regValue .rsi + BitVec.ofNat 64 i).toNat
  · exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
  · apply ctx.footprint_subset ⟨(l.sp initial - 344).toNat, 344⟩ (by simp [footprint]) _
    exact slot ⟨j, hj, same⟩

end Sha2.Proofs.Common.SHA256.Absorb
