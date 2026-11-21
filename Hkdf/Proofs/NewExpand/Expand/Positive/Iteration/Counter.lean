import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Clone
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Finish
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Prepare
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Stage

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256

structure Result [Bindings] (entry s t : RamState) (boundary : ReturnBoundary)
    (key message : ByteArray) (length n : Nat) : Prop extends SavedFrame entry t boundary length where
  pc : t.RIP = 0x10f95a
  hmac : HmacAt t (base entry + 80) key (message ++ singletonByte (UInt8.ofNat (n + 1)))
  remaining : slot t 8 = slot s 8 - slot s 264
  memcpy : t.regValue .r12 = 0x10dd60
  frameLocal : MemoryWriteFrame s t (writes entry)

set_option maxHeartbeats 900000 in
private theorem finish_and_clone [bindings : Bindings] {entry s u : RamState} {boundary : ReturnBoundary}
    {length n : Nat} {key message : ByteArray}
    (ctx : StackContext entry boundary length) (stride : UnitStringStride bindings)
    (saved : SavedFrame entry s boundary length)
    (staged : Staged entry s u boundary length key (message ++ singletonByte (UInt8.ofNat (n + 1))))
    (sp : stackPtr s = base entry) :
    ∃ t, Result entry s t boundary key message length n := by
  let next := message ++ singletonByte (UInt8.ofNat (n + 1))
  let tail := (innerMessage key next).size % 64
  obtain ⟨v, rv, spV, pcV, dxV, diV, siV, remV, byteV, frameV⟩ :=
    finish ctx staged.running staged.sp staged.pc staged.al
  have prefixLimit : tail < 64 := Nat.mod_lt _ (by decide)
  have smallFrame : MemoryWriteFrame u v #v[area entry 8 8, area entry 335 1] := by
    apply frameV.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · obtain ⟨i, hi, eq⟩ := ha
      exact ⟨_, by simp, eq ▸ contains_byte ctx.stack (off := 8) (by decide) (by decide) hi⟩
    · obtain ⟨i, hi, eq⟩ := ha
      exact ⟨_, by simp, eq ▸ contains_byte ctx.stack (off := 335) (by decide) (by decide) hi⟩
  have same (off size : Nat) (bound : off ≤ 536) (fit : off + size ≤ 544)
      (before : off + size ≤ 335 ∨ 336 ≤ off) (after : 16 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) size).Agrees u v := by
    apply area_agrees ctx.stack smallFrame bound fit
    intro r hr
    have cases : r = area entry 8 8 ∨ r = area entry 335 1 := by simpa using hr
    rcases cases with rfl | rfl
    · exact area_disjoint ctx.stack bound (by decide) (.inr after)
    · exact area_disjoint ctx.stack bound (by decide) before
  have bufV := staged.toBuffered.of_agreement
    (same 272 tail (by decide) (by omega) (.inl (by omega)) (by decide))
    (same 336 32 (by decide) (by decide) (.inr (by decide)) (by decide))
    (same 368 8 (by decide) (by decide) (.inr (by decide)) (by decide))
    (same 376 32 (by decide) (by decide) (.inr (by decide)) (by decide))
    (same 408 8 (by decide) (by decide) (.inr (by decide)) (by decide))
  have bxV : v.regValue .rbx = 0x10dd60 :=
    (frameV.read (n := 64) (r := 3) (by simp)).trans staged.copyReg
  obtain ⟨t, rt, pcT, spT, abi, hmacT, cloneFrame⟩ := clone ctx stride rv spV pcV bxV
    (siV.trans staged.context) (diV.trans staged.clonePtr) dxV (buffer_hmac bufV byteV)
  have cloneMemory : MemoryWriteFrame v t #v[area entry 80 144, scratch entry 8] := cloneFrame
  have remT := unchanged_slot spV spT (area_agrees ctx.stack cloneMemory
    (off := 8) (size := 8) (by decide) (by decide) (by
      intro r hm
      have cases : r = area entry 80 144 ∨ r = scratch entry 8 := by simpa using hm
      rcases cases with rfl | rfl
      · exact area_disjoint ctx.stack (by decide) (by decide) (.inl (by decide))
      · exact area_disjoint_scratch ctx.stack (by decide) (by decide)))
  have frameSmall : MemoryWriteFrame u v (writes entry) := by
    apply frame_mono smallFrame
    intro r hm a ha
    have cases : r = area entry 8 8 ∨ r = area entry 335 1 := by simpa using hm
    rcases cases with rfl | rfl
    · exact ⟨_, by simp [writes], ha⟩
    · exact ⟨area entry 272 104, by simp [writes],
        area_subset ctx.stack (by decide) (by decide) (by decide) (by decide) a ha⟩
  have frameClone : MemoryWriteFrame v t (writes entry) := by
    apply frame_mono cloneMemory
    intro r hm a ha
    have cases : r = area entry 80 144 ∨ r = scratch entry 8 := by simpa using hm
    rcases cases with rfl | rfl
    · exact ⟨_, by simp [writes], ha⟩
    · exact ⟨scratch entry 344, by simp [writes], scratch_subset ctx.stack (by decide) (by decide) a ha⟩
  have frame := memoryWriteFrame_trans (memoryWriteFrame_trans staged.frameLocal frameSmall) frameClone
  have chunk : slot u 264 = slot s 264 := unchanged_slot sp staged.sp
    (preserves_area ctx.stack staged.frameLocal (by decide) (by decide) (.inr (.inl (by decide))))
  have keep : (Component.mem (s.regValue .rsp + 488) 56).Agrees s t := by
    change (Component.mem (stackPtr s + 488) 56).Agrees s t
    rw [sp]
    exact preserves_area ctx.stack frame (off := 488) (by decide) (by decide) (.inr (.inr (by decide)))
  have keptSize : slot t 224 = slot s 224 := unchanged_slot sp spT
    (preserves_area ctx.stack frame (by decide) (by decide) (.inr (.inl (by decide))))
  have restored := saved.of_agreement rt (spT.trans sp.symm) keep keptSize
    (abi.2.2.1.trans ((frameV.mxcsr (by simp)).trans staged.mxcsr))
    (abi.2.2.2.trans ((frameV.fcw (by simp)).trans staged.fcw))
  exact ⟨t, restored, pcT, hmacT,
    remT.trans (remV.trans (by rw [staged.remaining, chunk])),
    (abi.1 .r12 (by simp)).trans ((frameV.read (n := 64) (r := 12) (by simp)).trans staged.memcpy), frame⟩

set_option maxHeartbeats 900000 in
theorem append [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info message : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (positive : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f8a0)
    (count : slot s 256 = BitVec.ofNat 64 n) (bound : n < 255)
    (memcpy : s.regValue .r12 = 0x10dd60) (hmac : HmacAt s (base entry + 272) key message) :
    ∃ t, Result entry s t boundary key message length n := by
  let tail := (innerMessage key message).size % 64
  let next := message ++ singletonByte (UInt8.ofNat (n + 1))
  let ctx := StackContext.of_pre pre positive limit
  have sp : stackPtr s = base entry := saved.sp
  have tailBound : tail < 64 := Nat.mod_lt _ (by decide)
  have tailByte : s.external[base entry + 335]? = some (UInt8.ofNat tail) := by
    rw [← tail_address]
    exact hmac.inner.tailLength
  obtain ⟨a, ra, spA, pcA, axA, clA, clonePtrA, byteA, frameA⟩ :=
    prepare ctx saved.toRunning sp pc count bound tailByte tailBound
  have localA : MemoryWriteFrame s a #v[area entry 80 1] := by
    apply agrees_write_frame ctx.stack (by decide) (by decide) frameA
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ha | exact ha.elim
  have sameA (off size : Nat) (bound : off ≤ 536) (fit : off + size ≤ 544)
      (apart : off + size ≤ 80 ∨ 81 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) size).Agrees s a := by
    apply area_agrees ctx.stack localA bound fit
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact area_disjoint ctx.stack bound (by decide) apart
  have bufA := (buffered_of_hmac hmac).of_agreement
    (sameA 272 tail (by decide) (by omega) (.inr (by decide)))
    (sameA 336 32 (by decide) (by decide) (.inr (by decide)))
    (sameA 368 8 (by decide) (by decide) (.inr (by decide)))
    (sameA 376 32 (by decide) (by decide) (.inr (by decide)))
    (sameA 408 8 (by decide) (by decide) (.inr (by decide)))
  have memcpyA : a.regValue .r12 = 0x10dd60 :=
    (frameA.read (n := 64) (r := 12) (by simp)).trans memcpy
  have stage : ∃ u, Staged entry a u boundary length key next := by
    by_cases full : tail = 63
    · exact stage_full ctx pre.call.stride ra spA (pcA.trans (ite_eq_left full))
        (axA.trans (congrArg (BitVec.ofNat 64) full)) full memcpyA clonePtrA bufA byteA
    · exact stage_short ctx ra spA (pcA.trans (ite_eq_right full)) axA clA (by
        change tail < 63
        omega) memcpyA clonePtrA bufA
  obtain ⟨u, state⟩ := stage
  have preserve8 : slot a 8 = slot s 8 := unchanged_slot sp spA
    (sameA 8 8 (by decide) (by decide) (.inl (by decide)))
  have frameAWide : MemoryWriteFrame s a (writes entry) := by
    apply frame_mono localA
    intro r hm x hx
    obtain rfl := Vector.mem_singleton.mp hm
    exact ⟨area entry 80 144, by simp [writes],
      area_subset ctx.stack (by decide) (by decide) (by decide) (by decide) x hx⟩
  have staged : Staged entry s u boundary length key next :=
    { state with
      mxcsr := state.mxcsr.trans (frameA.mxcsr (by simp))
      fcw := state.fcw.trans (frameA.fcw (by simp))
      remaining := state.remaining.trans preserve8
      frameLocal := memoryWriteFrame_trans frameAWide state.frameLocal }
  exact finish_and_clone ctx pre.call.stride saved staged sp

end Hkdf.Proofs.NewExpand.Expand.Counter
