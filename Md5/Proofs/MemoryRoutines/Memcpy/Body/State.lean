import Md5.Proofs.MemoryRoutines.Memcpy.Body.Frame
import Md5.Proofs.MemoryRoutines.Memcpy.Head
import Md5.Proofs.MemoryRoutines.Movsb
import Md5.Proofs.MemoryRoutines.Movsq

namespace Md5.Proofs.MemoryRoutines.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program Md5.Proofs.Block

structure CopyState [Bindings] (s t : RamState) (offset : Nat) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  source : rsi.read t = rsi.read s + BitVec.ofNat 64 offset
  destination : rdi.read t = rdi.read s + BitVec.ofNat 64 offset
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (copyChanges (rdi.read s) offset) s t
  copy : ∀ i < offset, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    s.external[rsi.read s + BitVec.ofNat 64 i]?

theorem CopyState.head [Bindings] {s t : RamState} (hr : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t) (he : (memcpyHeadEffect s).Holds s t) :
    CopyState s t 0 := by
  refine ⟨hr, hc, ?_, ?_, he.writes.1, ?_, ?_⟩
  · rw [he.agrees.read (by simp [memcpyHeadEffect, Effect.components, r8])]
    exact (BitVec.add_zero _).symm
  · rw [he.agrees.read (by simp [memcpyHeadEffect, Effect.components, r8])]
    exact (BitVec.add_zero _).symm
  · apply he.agrees.mono
    simp [memcpyHeadEffect, Effect.components, copyChanges, r8]
  · intro i hi
    omega

theorem CopyState.registers [Bindings] {s t u : RamState} {offset : Nat}
    (h : CopyState s t offset) (hr : ReadyToStep u)
    (ha : AgreesExcept [.reg 1, .reg 2, .flags, .rip] t u) : CopyState s u offset := by
  refine ⟨hr, ha.codeIn (by simp [Component.Covers]) h.code,
    (ha.read (by simp)).trans h.source, (ha.read (by simp)).trans h.destination,
    (ha.read (by simp)).trans h.result, ?_, ?_⟩
  · apply (h.agrees.trans ha).mono
    simp [copyChanges]
  · intro i hi
    rw [ha.byte (by simp [Component.Covers])]
    exact h.copy i hi

theorem CopyState.ranges [Bindings] {s u : RamState} {offset count : Nat}
    (h : CopyState s u offset) (hp : MemcpyPre s)
    (hb : offset + count ≤ (rdx.read s).toNat) :
    MemReadable u (rsi.read u) count ∧ WritableRange u (rdi.read u) count ∧
      ((rsi.read u).toNat + count ≤ (rdi.read u).toNat ∨
        (rdi.read u).toNat + count ≤ (rsi.read u).toNat) := by
  have hs := memReadable_slice hp.src offset count hb
  have hd := hp.dst.slice offset count hb
  refine ⟨?_, ?_, ?_⟩
  · rw [h.source]
    exact ⟨hs.low, fun i hi ↦ h.agrees.grow _ (hs.mem i hi)⟩
  · rw [h.destination]
    exact hd.of_agrees h.agrees
  · rw [h.source, h.destination,
      toNat_add_ofNat _ _ (by have := hp.src.low; omega),
      toNat_add_ofNat _ _ (by have := hp.dst.readable.low; omega)]
    have := hp.disjoint
    omega

theorem CopyState.append [Bindings] {s u t : RamState} {offset count : Nat}
    (h : CopyState s u offset) (hp : MemcpyPre s)
    (hb : offset + count ≤ (rdx.read s).toNat) (hr : ReadyToStep t)
    (hs : rsi.read t = rsi.read u + BitVec.ofNat 64 count)
    (hd : rdi.read t = rdi.read u + BitVec.ofNat 64 count)
    (hc : ∀ i < count, t.external[rdi.read u + BitVec.ofNat 64 i]? =
      u.external[rsi.read u + BitVec.ofNat 64 i]?)
    (ha : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read u) count, .rip] u t) :
    CopyState s t (offset + count) := by
  have haw : AgreesExcept
      (copyChanges (rdi.read s + BitVec.ofNat 64 offset) count) u t := by
    rw [← h.destination]
    apply ha.mono
    simp [copyChanges]
  have hfull := copyChanges_trans h.agrees haw
  refine ⟨hr, ?_, ?_, ?_, (ha.read (by simp)).trans h.result, hfull, ?_⟩
  · exact copyChanges_code haw ((hp.dst.slice offset count hb).of_agrees h.agrees) h.code
  · rw [hs, h.source, add_ofNat_add_ofNat]
  · rw [hd, h.destination, add_ofNat_add_ofNat]
  · apply copy_append h.copy
    · simpa only [h.destination, h.source] using hc
    · intro i hi
      rw [add_ofNat_add_ofNat]
      exact copyChanges_source hp (by omega) h.agrees (offset + i) (by omega)
    · exact copyChanges_prefix (by have := hp.dst.readable.low; omega) haw



theorem CopyState.movsb [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s u : RamState} {offset : Nat} (h : CopyState s u offset) (hp : MemcpyPre s)
    (p : BitVec 64) (hip : u.RIP = p) (hc : CodeIn (codeRange p [0xf3, 0xa4]) u)
    (htext : ∀ i < 2, InProgram (p + BitVec.ofNat 64 i))
    (hbound : offset + (rcx.read u).toNat ≤ (rdx.read s).toNat)
    (boundary : ReturnBoundary) (hstart : p ≠ boundary.rip)
    (hend : p + 2#64 ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel u t ∧
      CopyState s t (offset + (rcx.read u).toNat) ∧ t.RIP = p + 2#64 ∧
      AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read u) (rcx.read u).toNat, .rip] u t := by
  obtain ⟨hrs, hwd, hdis⟩ := h.ranges hp hbound
  have hpre : Movsb.RepMovsbPre p u :=
    ⟨hip, (h.agrees.directionFlagClear (by simp [copyChanges]) ⟨hp.df⟩).df, hrs.low,
      hwd.readable.low,
      hrs.mem, hwd.readable.mem, hdis, hwd.tables,
      fun i hi j hj he ↦ hwd.code i hi (he ▸ htext j hj)⟩
  have hd := Movsb.rep_movsb_done hstride p u h.ready hc hpre
  have ha := Movsb.rep_movsb_advances hstride boundary p u h.ready hc hpre hstart hend
  have hag := Movsb.rep_movsb_agrees hstride p u h.ready hc hpre
  exact ⟨_, _, ha, h.append hp hbound hd.ready hd.rsiAfter hd.rdiAfter hd.copy hag,
    hd.rip.trans (congrArg (· + 2#64) hip), hag⟩

theorem CopyState.movsq [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s u : RamState} {offset : Nat} (h : CopyState s u offset) (hp : MemcpyPre s)
    (p : BitVec 64) (hip : u.RIP = p) (hc : CodeIn (codeRange p [0xf3, 0x48, 0xa5]) u)
    (htext : ∀ i < 3, InProgram (p + BitVec.ofNat 64 i))
    (hbound : offset + 8 * (rcx.read u).toNat ≤ (rdx.read s).toNat)
    (halign : 0 < (rcx.read u).toNat → (rdi.read u).toNat % 8 = 0)
    (boundary : ReturnBoundary) (hstart : p ≠ boundary.rip)
    (hend : p + 3#64 ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel u t ∧
      CopyState s t (offset + 8 * (rcx.read u).toNat) ∧ t.RIP = p + 3#64 ∧
      AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read u) (8 * (rcx.read u).toNat), .rip]
        u t := by
  obtain ⟨hrs, hwd, hdis⟩ := h.ranges hp hbound
  have hpre : Movsq.RepMovsqPre p u :=
    ⟨hip, (h.agrees.directionFlagClear (by simp [copyChanges]) ⟨hp.df⟩).df, hrs.low,
      hwd.readable.low,
      halign, hrs.mem, hwd.readable.mem, hdis, hwd.tables,
      fun i hi j hj he ↦ hwd.code i hi (he ▸ htext j hj)⟩
  have hrex : RexWPrefix (0x48 : UInt8).toBitVec := by unfold RexWPrefix; decide
  have hd := Movsq.rep_movsq_done hstride p 0x48 hrex u h.ready hc hpre
  have ha := Movsq.rep_movsq_advances hstride boundary p 0x48 hrex u h.ready hc hpre hstart hend
  have hag := Movsq.rep_movsq_agrees hstride p 0x48 hrex u h.ready hc hpre
  exact ⟨_, _, ha, h.append hp hbound hd.ready hd.rsiAfter hd.rdiAfter hd.copy hag,
    hd.rip.trans (congrArg (· + 3#64) hip), hag⟩

end Md5.Proofs.MemoryRoutines.Memcpy
