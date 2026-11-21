import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Buffer
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Compress
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Full
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Short

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256

structure Staged [Bindings] (entry s t : RamState) (boundary : ReturnBoundary) (length : Nat)
    (key message : ByteArray) : Prop extends Buffered entry t key message where
  running : RunningFrame entry boundary length t
  sp : stackPtr t = base entry
  pc : t.RIP = 0x10f934
  al : (t.regValue .rax).setWidth 8 = (UInt8.ofNat ((innerMessage key message).size % 64)).toBitVec
  copyReg : t.regValue .rbx = 0x10dd60
  memcpy : t.regValue .r12 = 0x10dd60
  context : t.regValue .r14 = base entry + 272
  clonePtr : t.regValue .r15 = base entry + 80
  mxcsr : t.MXCSR = s.MXCSR
  fcw : t.FP87_Control = s.FP87_Control
  remaining : slot t 8 = slot s 8
  frameLocal : MemoryWriteFrame s t (writes entry)

private theorem widen_one {entry s t : RamState} {off size : Nat}
    (frame : MemoryWriteFrame s t #v[area entry off size])
    (stack : Stack.Valid entry 2264) (lo : 272 ≤ off) (bound : off + size ≤ 376) :
    MemoryWriteFrame s t (writes entry) := by
  apply frame_mono frame
  intro r hr a ha
  obtain rfl := Vector.mem_singleton.mp hr
  exact ⟨area entry 272 104, by simp [writes], area_subset stack (by omega) (by decide) lo (by omega) a ha⟩

private theorem widen_scratch {entry s t : RamState} {off size depth : Nat}
    (frame : MemoryWriteFrame s t #v[area entry off size, scratch entry depth])
    (stack : Stack.Valid entry 2264) (lo : 272 ≤ off) (bound : off + size ≤ 376)
    (scratchBound : depth ≤ 344) :
    MemoryWriteFrame s t (writes entry) := by
  apply frame_mono frame
  intro r hr a ha
  have cases : r = area entry off size ∨ r = scratch entry depth := by simpa using hr
  rcases cases with rfl | rfl
  · exact ⟨area entry 272 104, by simp [writes], area_subset stack (by omega) (by decide) lo (by omega) a ha⟩
  · exact ⟨scratch entry 344, by simp [writes], scratch_subset stack scratchBound (by decide) a ha⟩

set_option maxHeartbeats 800000 in
theorem stage_short [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key message : ByteArray} {b : UInt8}
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (sp : stackPtr s = base entry) (pc : s.RIP = 0x10f920)
    (ax : s.regValue .rax = BitVec.ofNat 64 ((innerMessage key message).size % 64))
    (cl : (s.regValue .rcx).setWidth 8 = b.toBitVec)
    (shortTail : (innerMessage key message).size % 64 < 63)
    (memcpy : s.regValue .r12 = 0x10dd60) (clonePtr : s.regValue .r15 = base entry + 80)
    (buf : Buffered entry s key message) :
    ∃ t, Staged entry s t boundary length key (message ++ singletonByte b) := by
  let m := innerMessage key message
  let tail := m.size % 64
  change tail < 63 at shortTail
  change s.regValue .rax = BitVec.ofNat 64 tail at ax
  obtain ⟨t, rt, spT, pcT, axT, copyT, context, byte, effect⟩ :=
    short ctx running sp pc shortTail ax cl
  have localFrame : MemoryWriteFrame s t #v[area entry (272 + tail) 1] := by
    apply agrees_write_frame ctx.stack (by omega) (by omega) effect
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ha | exact ha.elim
  have unchanged (off width : Nat) (bound : off ≤ 536) (fit : off + width ≤ 544)
      (apart : off + width ≤ 272 + tail ∨ 273 + tail ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees s t := by
    apply area_agrees ctx.stack localFrame bound fit
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact area_disjoint ctx.stack bound (by omega) (by omega)
  have nofull : ¬ m.size % 64 = 63 := by change tail ≠ 63; omega
  have append : innerMessage key (message ++ singletonByte b) = m ++ singletonByte b :=
    ByteArray.append_assoc.symm
  have quotient : (innerMessage key (message ++ singletonByte b)).size / 64 = m.size / 64 := by
    rw [append, quotient_append_byte, ite_eq_right nofull, Nat.add_zero]
  have remSize : (innerMessage key (message ++ singletonByte b)).size % 64 = tail + 1 := by
    rw [append, remainder_size_append_byte, ite_eq_right nofull]
  have rem : remainderBytes (innerMessage key (message ++ singletonByte b)) =
      remainderBytes m ++ singletonByte b := by
    rw [append, remainder_append_byte, ite_eq_right nofull]
  have hash : compressBlocks initialHash (innerMessage key (message ++ singletonByte b)) =
      compressBlocks initialHash m := by
    rw [append, compressBlocks_append_short]
    change 1 < 64 - tail
    omega
  have bufT : Buffered entry t key (message ++ singletonByte b) := by
    refine ⟨?_, ?_, ?_, hashState_of_bytes buf.outerWords (unchanged 376 32 (by decide) (by decide) (.inr (by omega))),
      (Memory.loadBytes_congr (unchanged 408 8 (by decide) (by decide) (.inr (by omega)))).trans buf.outerBlocks⟩
    · rw [hash]
      exact hashState_of_bytes buf.words (unchanged 336 32 (by decide) (by decide) (.inr (by omega)))
    · rw [remSize, rem]
      exact tail_with_byte buf.tail (unchanged 272 tail (by decide) (by omega) (.inl (by omega))) byte
    · rw [quotient]
      exact (Memory.loadBytes_congr (unchanged 368 8 (by decide) (by decide) (.inr (by omega)))).trans buf.blocks
  refine ⟨t, bufT, rt, spT, pcT, ?_, copyT.trans memcpy,
    (effect.read (n := 64) (r := 12) (by simp)).trans memcpy, context,
    (effect.read (n := 64) (r := 15) (by simp)).trans clonePtr,
    effect.mxcsr (by simp), effect.fcw (by simp),
    unchanged_slot sp spT (unchanged 8 8 (by decide) (by decide) (.inl (by omega))), widen_one localFrame ctx.stack (by omega) (by omega)⟩
  rw [axT, remSize]
  apply BitVec.eq_of_toNat_eq
  change ((BitVec.ofNat 64 (tail + 1)).setWidth 8).toNat = (BitVec.ofNat 8 (tail + 1)).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 900000 in
theorem stage_full [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key message : ByteArray} {b : UInt8}
    (ctx : StackContext entry boundary length) (stride : UnitStringStride bindings)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry) (pc : s.RIP = 0x10f8ce)
    (ax : s.regValue .rax = 63) (fullTail : (innerMessage key message).size % 64 = 63)
    (memcpy : s.regValue .r12 = 0x10dd60) (clonePtr : s.regValue .r15 = base entry + 80)
    (buf : Buffered entry s key message) (byte : s.external[base entry + 80]? = some b) :
    ∃ t, Staged entry s t boundary length key (message ++ singletonByte b) := by
  let m := innerMessage key message
  change m.size % 64 = 63 at fullTail
  obtain ⟨u, ru, spU, pcU, bxU, r12U, r13U, r15U, bpU, mxU, fcU, byteU, frameU⟩ :=
    copy_byte ctx stride running sp pc ax memcpy clonePtr byte
  have copySame (off width : Nat) (bound : off ≤ 536) (fit : off + width ≤ 544)
      (apart : off + width ≤ 335 ∨ 336 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees s u := by
    apply area_agrees ctx.stack (show MemoryWriteFrame s u #v[area entry 335 1, scratch entry 8] from frameU)
      bound fit
    intro r hr
    have cases : r = area entry 335 1 ∨ r = scratch entry 8 := by simpa using hr
    rcases cases with rfl | rfl
    · exact area_disjoint ctx.stack bound (by decide) (by omega)
    · exact area_disjoint_scratch ctx.stack bound (by decide)
  let block := remainderBytes m ++ singletonByte b
  have blockU : (area entry 272 64).HasBytes u.external block := by
    have tail : (area entry 272 63).HasBytes s.external (remainderBytes m) := fullTail ▸ buf.tail
    exact tail_with_byte tail (copySame 272 63 (by decide) (by decide) (.inl (by decide))) byteU
  obtain ⟨v, rv, _, spV, pcV, inc, effectV⟩ := increment_blocks ctx ru spU pcU
  have frameV : MemoryWriteFrame u v #v[area entry 368 8] := by
    apply agrees_write_frame ctx.stack (by decide) (by decide) effectV
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha
    · exact ha.elim
    · exact ha.elim
  have incSame (off width : Nat) (bound : off ≤ 536) (fit : off + width ≤ 544)
      (apart : off + width ≤ 368 ∨ 376 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees u v := by
    apply area_agrees ctx.stack frameV bound fit
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact area_disjoint ctx.stack bound (by decide) (by omega)
  have blockV : (area entry 272 64).HasBytes v.external block := by
    refine frame_hasBytes frameV ?_ ?_ blockU
    · intro r hr
      obtain rfl := Vector.mem_singleton.mp hr
      exact area_disjoint ctx.stack (by decide) (by decide) (.inl (by decide))
    · have h := area_bounded ctx.stack (off := 272) (size := 64) (by decide) (by decide)
      change (area entry 272 64).start + 64 ≤ 2^64
      change (area entry 272 64).start + 64 < 2^32 at h
      omega
  have wordsV := hashState_of_bytes buf.words
    ((copySame 336 32 (by decide) (by decide) (.inr (by decide))).trans
      (incSame 336 32 (by decide) (by decide) (.inl (by decide))))
  obtain ⟨t, rt, spT, pcT, axT, context, kept, mxT, fcT, wordsT, frameT⟩ :=
    compress ctx stride rv spV pcV wordsV blockV
  have compSame (off width : Nat) (bound : off ≤ 536) (fit : off + width ≤ 544)
      (apart : off + width ≤ 336 ∨ 368 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees v t := by
    apply area_agrees ctx.stack (show MemoryWriteFrame v t #v[area entry 336 32, scratch entry 344] from frameT)
      bound fit
    intro r hr
    have cases : r = area entry 336 32 ∨ r = scratch entry 344 := by simpa using hr
    rcases cases with rfl | rfl
    · exact area_disjoint ctx.stack bound (by decide) (by omega)
    · exact area_disjoint_scratch ctx.stack bound (by decide)
  have append : innerMessage key (message ++ singletonByte b) = m ++ singletonByte b :=
    ByteArray.append_assoc.symm
  have quotient : (innerMessage key (message ++ singletonByte b)).size / 64 = m.size / 64 + 1 := by
    rw [append, quotient_append_byte, ite_eq_left fullTail]
  have remSize : (innerMessage key (message ++ singletonByte b)).size % 64 = 0 := by
    rw [append, remainder_size_append_byte, ite_eq_left fullTail]
  have rem : remainderBytes (innerMessage key (message ++ singletonByte b)) = ByteArray.empty := by
    rw [append, remainder_append_byte, ite_eq_left fullTail]
  have hash : compressBlocks initialHash (innerMessage key (message ++ singletonByte b)) =
      compressBlocks (compressBlocks initialHash m) block := by
    rw [append, compressBlocks_append_buffered]
  have oldBlocks := unchanged_slot sp spU (copySame 368 8 (by decide) (by decide) (.inr (by decide)))
  have baseBlocks : slot s 368 = BitVec.ofNat 64 (m.size / 64) := by
    change memLoad s.external (stackPtr s + 368) 64 = _
    rw [sp]
    exact Memory.memLoad_of_loadBytes64 buf.blocks
  have newBlocks : loadBytes t.external (base entry + 368) 8 = .ok (BitVec.ofNat 64 (m.size / 64 + 1)) := by
    have vBlocks : loadBytes v.external (base entry + 368) 8 = .ok (BitVec.ofNat 64 (m.size / 64 + 1)) := by
      have writable := read_stack ctx rv (off := 368) (size := 8) (by decide) (by decide)
      have b := Bytes.of_memLoad (n := 64) writable.mem
      have after : memLoad v.external (base entry + 368#64) 64 = BitVec.ofNat 64 (m.size / 64 + 1) := by
        exact inc.trans ((congrArg (· + 1) (oldBlocks.trans baseBlocks)).trans (by rw [BitVec.ofNat_add]; rfl))
      rw [after] at b
      exact b.loadBytes64
    exact (Memory.loadBytes_congr (compSame 368 8 (by decide) (by decide) (.inr (by decide)))).trans vBlocks
  have outerSame (off width : Nat) (bound : off ≤ 536) (fit : off + width ≤ 544) (lo : 376 ≤ off) :
      (Component.mem (base entry + BitVec.ofNat 64 off) width).Agrees s t :=
    ((copySame off width bound fit (.inr (by omega))).trans (incSame off width bound fit (.inr lo))).trans
      (compSame off width bound fit (.inr (by omega)))
  have bufT : Buffered entry t key (message ++ singletonByte b) := by
    refine ⟨?_, ?_, ?_, hashState_of_bytes buf.outerWords (outerSame 376 32 (by decide) (by decide) (by decide)),
      (Memory.loadBytes_congr (outerSame 408 8 (by decide) (by decide) (by decide))).trans buf.outerBlocks⟩
    · rw [hash]
      exact wordsT
    · rw [remSize, rem]
      exact ⟨rfl, fun i => Fin.elim0 i⟩
    · rw [quotient]
      exact newBlocks
  have allWrites := memoryWriteFrame_trans
    (memoryWriteFrame_trans (widen_scratch frameU ctx.stack (by decide) (by decide) (by decide))
      (widen_one frameV ctx.stack (by decide) (by decide)))
    (widen_scratch frameT ctx.stack (by decide) (by decide) (by decide))
  have remaining := unchanged_slot sp spT
    (((copySame 8 8 (by decide) (by decide) (.inl (by decide))).trans
      (incSame 8 8 (by decide) (by decide) (.inl (by decide)))).trans
      (compSame 8 8 (by decide) (by decide) (.inl (by decide))))
  refine ⟨t, bufT, rt, spT, pcT, ?_,
    (kept .rbx (by simp)).trans ((effectV.read (n := 64) (r := 3) (by simp)).trans bxU),
    (kept .r12 (by simp)).trans ((effectV.read (n := 64) (r := 12) (by simp)).trans (r12U.trans memcpy)),
    context, (kept .r15 (by simp)).trans ((effectV.read (n := 64) (r := 15) (by simp)).trans (r15U.trans clonePtr)),
    mxT.trans ((effectV.mxcsr (by simp)).trans mxU), fcT.trans ((effectV.fcw (by simp)).trans fcU), remaining, allWrites⟩
  rw [axT, remSize]
  rfl

end Hkdf.Proofs.NewExpand.Expand.Counter
