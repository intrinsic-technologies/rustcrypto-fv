import Sha2.Proofs.Common.SHA256.Absorb.Proof.Compression
import Sha2.Proofs.Common.Machine.AfterStackCall

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem call_byte {s u : RamState} {target : RamState → BitVec 64} {ret base : BitVec 64}
    {len i : Nat} (effect : (callEffect target ret s).Holds s u)
    (apart : RangeApart base len (pushAddr s) 8) (bound : i < len) :
    u.external[base + BitVec.ofNat 64 i]? = s.external[base + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c member covered
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · obtain ⟨j, hj, equal⟩ := covered
    exact apart i bound j hj equal
  · exact covered.elim

theorem Context.buffer_push_apart [Bindings] {l : Layout} {initial s : RamState}
    {n reserve offset len : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (rsp : stackPtr s = l.sp initial)
    (bound : offset + len ≤ 104) :
    RangeApart (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len (pushAddr s) 8 := by
  have capacity := ctx.wf.capacity
  have fits := ctx.wf.bufferFits
  have bounds := stack_valid_bounds ctx.stack
  have address : l.buffer (l.sp initial) + BitVec.ofNat 64 offset =
      pushAddr s + BitVec.ofNat 64 (8 + l.bufferOffset + offset) := by
    rw [pushAddr, rsp, BitVec.ofNat_add, BitVec.ofNat_add]
    simp only [Layout.buffer, ← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat]
  rw [address]
  simpa only [BitVec.add_zero] using RangeApart.offsets (pushAddr s)
    (a := 8 + l.bufferOffset + offset) (len := len) (b := 0) (count := 8)
    (by omega) (by decide) (.inr (by omega))

theorem Context.compression_pre [Bindings] {l : Layout} {initial s u : RamState}
    {n reserve count : Nat} {regions : Vector MemoryRegion n} {ret : BitVec 64}
    {hash : Array UInt32} {chunk : ByteArray}
    (ctx : Context l initial regions reserve) (rsp : stackPtr s = l.sp initial)
    (output : s.regValue .rdi = l.buffer (l.sp initial) + 64)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (bytes : (registerRegion s .rsi (64 * count)).HasBytes s.external chunk)
    (words : HashStateAt s (l.buffer (l.sp initial) + 64) hash)
    (apart : RangeApart (s.regValue .rsi) (64 * count) (pushAddr s) 8)
    (effect : (callEffect (fun _ => 0x10b4e0) ret s).Holds s u)
    (callee : CalleePre u (returnBoundary initial) 0x10b4e0 (64 * count) 32 336) :
    CompressionPre u (returnBoundary initial) hash chunk count := by
  have outputU : u.regValue .rdi = l.buffer (l.sp initial) + 64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans output
  have sourceU : u.regValue .rsi = s.regValue .rsi :=
    effect.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])
  refine ⟨callee, ?_, ?_, ?_⟩
  · exact (effect.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans length
  · refine ⟨bytes.1, ?_⟩
    intro i
    have hi : i.val < 64 * count := by have := i.isLt; have size : chunk.size = 64 * count := bytes.1; omega
    simpa only [registerRegion, sourceU, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using
      (call_byte effect apart hi).trans (by
        simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
          BitVec.setWidth_eq] using bytes.2 i)
  · rw [outputU]
    apply Wrapper.hashState_of_bytes words
    intro i hi
    exact call_byte effect (ctx.buffer_push_apart rsp (by decide : 64 + 32 ≤ 104)) hi

theorem Context.bulk_pre [Bindings] {l : Layout} {initial s u : RamState}
    {n reserve count : Nat} {regions : Vector MemoryRegion n} {ret : BitVec 64}
    {hash : Array UInt32} {chunk : ByteArray}
    (ctx : Context l initial regions reserve) (state : ExecutionState initial s regions)
    (rsp : stackPtr s = l.sp initial)
    (output : s.regValue .rdi = l.buffer (l.sp initial) + 64)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (bytes : (registerRegion s .rsi (64 * count)).HasBytes s.external chunk)
    (bounded : (registerRegion s .rsi (64 * count)).Bounded)
    (apart : (registerRegion s .rsi (64 * count)).Disjoint (Stack.region initial reserve))
    (words : HashStateAt s (l.buffer (l.sp initial) + 64) hash)
    (inside : InProgram ret) (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x10b4e0) ret s).Holds s u) :
    CompressionPre u (returnBoundary initial) hash chunk count := by
  have fits := ctx.wf.bufferFits
  have capacity := ctx.wf.capacity
  refine ctx.compression_pre rsp output length bytes words ?_ effect ?_
  · intro i hi j hj equal
    apply apart (s.regValue .rsi + BitVec.ofNat 64 i).toNat
    · exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
    · apply ctx.footprint_subset ⟨(l.sp initial - 344).toNat, 344⟩ (by simp [footprint]) _
      apply call_slot_contains ctx.stack capacity
      simpa only [pushAddr, rsp, Layout.sp] using (show
        (Component.mem (pushAddr s) 8).Covers (s.regValue .rsi + BitVec.ofNat 64 i) from ⟨j, hj, equal⟩)
  · apply callee_pre_after_call (outputOffset := l.frameBytes - (l.bufferOffset + 64))
      (outputBytes := 32) (reserve := 336)
      ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress state rsp ?_
      ctx.wf.aligned (by omega) (by omega) (by omega) bounded
      (Common.Memory.hasBytes_allocated bytes) apart ready effect inside
    rw [output]
    simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using stack_frame_address initial
      (by omega : l.bufferOffset + 64 ≤ l.frameBytes)

theorem Context.fill_pre [Bindings] {l : Layout} {initial s u : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {ret : BitVec 64}
    {hash : Array UInt32} {chunk : ByteArray}
    (ctx : Context l initial regions reserve) (state : ExecutionState initial s regions)
    (rsp : stackPtr s = l.sp initial) (source : s.regValue .rsi = l.buffer (l.sp initial))
    (output : s.regValue .rdi = l.buffer (l.sp initial) + 64)
    (length : s.regValue .rdx = 1)
    (bytes : (⟨(l.buffer (l.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk)
    (words : HashStateAt s (l.buffer (l.sp initial) + 64) hash)
    (inside : InProgram ret) (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x10b4e0) ret s).Holds s u) :
    CompressionPre u (returnBoundary initial) hash chunk 1 := by
  have fits := ctx.wf.bufferFits
  have capacity := ctx.wf.capacity
  refine ctx.compression_pre rsp output length (by simpa only [registerRegion, source, Nat.mul_one] using bytes)
    words ?_ effect ?_
  · simpa only [source, BitVec.add_zero, Nat.mul_one] using
      ctx.buffer_push_apart rsp (by decide : 0 + 64 ≤ 104)
  · let layout : Wrapper.StackCallLayout reserve 64 32 336 :=
      ⟨l.frameBytes + 8, l.frameBytes - l.bufferOffset, l.frameBytes - (l.bufferOffset + 64),
        ctx.wf.aligned, by omega, by omega, by omega, by omega, by omega, .inl (by omega)⟩
    apply callee_pre_after_stack_call ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress
      state layout rfl rsp ?_ ?_ ready effect inside
    · rw [source]
      exact stack_frame_address initial (by omega)
    · rw [output]
      simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat] using stack_frame_address initial
        (by omega : l.bufferOffset + 64 ≤ l.frameBytes)

end Sha2.Proofs.Common.SHA256.Absorb
