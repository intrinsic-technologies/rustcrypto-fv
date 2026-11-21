import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Bookkeeping
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Inner.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Inner.Length

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Inner

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.StreamPadding
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Result [Bindings] (entry s t : RamState) (boundary : ReturnBoundary)
    (length : Nat) (message : ByteArray) (hash : Array UInt32) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  saved : SavedFrame entry t boundary length
  rip : t.RIP = 0x10f3bd
  rsp : stackPtr t = stackPtr s
  rbx : t.regValue .rbx = slot s 264
  r14 : t.regValue .r14 = slot s 432
  rbp : t.regValue .rbp = slot s 432 + slot s 264
  r12 : t.regValue .r12 = s.regValue .r12
  r13 : t.regValue .r13 = stackPtr s + 16
  r15 : t.regValue .r15 = stackPtr s + 144
  counter : slot t 256 = slot s 256 + 1
  frame : MemoryWriteFrame s t (writes (stackPtr s))
  hashWords : HashStateAt t (stackPtr t + 144)
    (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits (finalBlock message)))

private theorem length_pre [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (saved : SavedFrame entry s boundary length)
    (rip : s.RIP = 0x10f33c) : LengthPre s := by
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have address (o : Nat) (fit : o ≤ 536) :
      rspOf s + BitVec.ofNat 64 o = stackPtr entry - BitVec.ofNat 64 (536 - o) :=
    InnerPadding.local_address sp o fit
  have bounds (o : Nat) (member : o ∈ ([136,72] : List Nat)) :
      o ≤ 136 ∧ (536 - o) % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  refine ⟨rip, ?_, ?_⟩
  · intro o member
    obtain ⟨fit, aligned⟩ := bounds o member
    rw [address o (by omega)]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid saved.allocated (by omega) aligned
  · intro o member off len bytes
    have fit := (bounds o member).1
    rw [address o (by omega)]
    change RangeApart _ _ ((Extracted.textAddress + BitVec.ofNat 64 0xf33c) + _) _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stack_codeApart pre.call.stack (fun a ha hp ↦ pre.call.stackAvoid a ha (.inl hp))
      (by omega) (by omega) (by omega)

private theorem same_bytes {s t : RamState} {sp : BitVec 64} {off size : Nat}
    {bytes : ByteArray} (same : (Component.mem (sp + BitVec.ofNat 64 off) size).Agrees s t)
    (source : (⟨(sp + BitVec.ofNat 64 off).toNat, size⟩ : MemoryRegion).HasBytes s.external bytes) :
    (⟨(sp + BitVec.ofNat 64 off).toNat, size⟩ : MemoryRegion).HasBytes t.external bytes := by
  refine ⟨source.1, fun i ↦ ?_⟩
  have sizeEq : bytes.size = size := source.1
  have hi : i.val < size := sizeEq ▸ i.isLt
  have byte := (same i.val hi).trans (by
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using source.2 i)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte

theorem run [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info message : ByteArray} {ptr : BitVec 64} {length : Nat} {hash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f320)
    (prefixBytes : (⟨(stackPtr s + 80).toNat, 56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message))
    (remainder : s.regValue .r15 = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue .r13 = BitVec.ofNat 64 (message.size / 64))
    (words : HashStateAt s (stackPtr s + 144) hash) :
    ∃ t, Result entry s t boundary length message hash := by
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  obtain ⟨lo, high⟩ := local_bounds pre.call.stack sp
  obtain ⟨bookFuel, b, bookRun, bReady, bRip, bR14, bRBX, bRBP, bCounter, bEffect⟩ :=
    bookkeeping pre saved pc
  have bookWrites : StackWrites
      [.reg 14, .reg 3, .reg 5, .mem (stackPtr s + 256) 8, .flags, .rip]
      (stackPtr s) [(256, 8)] := by
    intro c member a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨(256, 8), by simp, covered⟩
  have bSaved := (bookWrites.saved pre pos bound saved bookRun bReady bEffect
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; decide) (by simp)).1
  have bSP : stackPtr b = stackPtr s := bEffect.read (n := 64) (r := 4) (by simp)
  have bRem : b.regValue .r15 = BitVec.ofNat 64 (message.size % 64) :=
    (bEffect.read (n := 64) (r := 15) (by simp)).trans remainder
  have bBlocks : b.regValue .r13 = BitVec.ofNat 64 (message.size / 64) :=
    (bEffect.read (n := 64) (r := 13) (by simp)).trans blocks
  have bPrefix : (⟨(stackPtr b + 80).toNat, 56⟩ : MemoryRegion).HasBytes
      b.external (finalPrefix message) := by
    rw [bSP]
    exact same_bytes (bookWrites.agrees bEffect (off := 80) (by decide)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)) prefixBytes
  have bHash : HashStateAt b (stackPtr b + 144) hash := by
    rw [bSP]
    exact hashState_of_bytes words (bookWrites.agrees bEffect (off := 144) (len := 32)
      (by decide) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; decide))
  obtain ⟨lenFuel, l, lenRun, lReady, lEffect⟩ := storeLength bReady bSaved.loaded
    pre.call.outerBoundary (length_pre pre bSaved bRip)
  have lenWrites := length_footprint b
  have lSaved := (lenWrites.saved pre pos bound bSaved lenRun lReady lEffect.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide) (by simp [length_components])).1
  have lSP : stackPtr l = stackPtr b :=
    lEffect.agrees.read (n := 64) (r := 4) (by simp [length_components])
  have lWords := length_slots lEffect bRem bBlocks
  have lRead : MemReadable l (stackPtr b + 136) 8 := by
    have spB : stackPtr b = stackPtr entry - 536 := bSaved.sp
    change MemReadable l (stackPtr b + BitVec.ofNat 64 136) 8
    rw [InnerPadding.local_address spB 136 (by decide)]
    exact stack_readable pre.call.stack lSaved.allocated (by decide) (by decide)
  have lBytes : (⟨(stackPtr l + 80).toNat, 64⟩ : MemoryRegion).HasBytes
      l.external (finalBlock message) := by
    rw [lSP]
    exact block_bytes bPrefix lEffect lRead lWords.1
  have lEighth : slot l 72 = slot l 136 := by
    change memLoad l.external (stackPtr l + 72) 64 = memLoad l.external (stackPtr l + 136) 64
    rw [lSP]
    exact lWords.2
  have lenBound (r : Nat × Nat) (member : r ∈ ([(136,8),(72,8)] : List (Nat × Nat))) :
      r.1 + r.2 ≤ 2^64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  have lHash : HashStateAt l (stackPtr l + 144) hash := by
    rw [lSP]
    exact hashState_of_bytes bHash (lenWrites.agrees lEffect.agrees (off := 144) (len := 32)
      (by decide) lenBound (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide))
  have lCounter : slot l 256 = slot s 256 + 1 := by
    change memLoad l.external (stackPtr l + 256) 64 = _
    rw [lSP]
    exact (agrees_memLoad (lenWrites.agrees lEffect.agrees (off := 256) (len := 8)
      (by decide) lenBound (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide))).trans bCounter
  have avoids : ∀ r ∈ #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264],
      r.Avoids InProgram := by
    simp only [writtenLength, bound, ↓reduceIte]
    exact fun r hr a ha hp ↦ ((pre.separation pos bound).2 r hr).2 a ha (.inl hp)
  obtain ⟨t, tRun, tRip, tSP, abi, tMXCSR, tFCW, tHash⟩ :=
    compressBlock pre lSaved.toRunning (by simp) avoids lSaved.sp .inner lEffect.rip
      (by intro impossible; cases impossible) lBytes lEighth lHash
  have lSpS : stackPtr l = stackPtr s := lSP.trans bSP
  have tSpS : stackPtr t = stackPtr s := tSP.trans lSpS
  have bFrame : MemoryWriteFrame s b (writes (stackPtr s)) :=
    precise_effect high bEffect bookWrites (by
      intro r hr
      exact Or.inr (Or.inr (List.mem_singleton.mp hr)))
  have lFrame : MemoryWriteFrame b l (writes (stackPtr s)) := by
    rw [← bSP]
    apply precise_effect (bSP ▸ high) lEffect.agrees lenWrites
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have cFrame : MemoryWriteFrame l t (writes (stackPtr s)) := by
    rw [← lSpS]
    exact compression_frame (lSpS ▸ high) tRun.frame
  have frame := memoryWriteFrame_trans bFrame (memoryWriteFrame_trans lFrame cFrame)
  have counter : slot t 256 = slot s 256 + 1 := by
    change memLoad t.external (stackPtr t + 256) 64 = _
    rw [tSP]
    exact (agrees_memLoad (compression_counter (lSpS ▸ lo) (lSpS ▸ high) tRun.frame)).trans lCounter
  obtain ⟨cFuel, cRun⟩ := tRun.execution
  have execution : Advances boundary (bookFuel + lenFuel + cFuel) s t :=
    (bookRun.trans lenRun).trans cRun
  have global : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t := by
    obtain ⟨prior, priorRun⟩ := saved.execution
    exact ⟨⟨prior + _, priorRun.trans execution⟩, tRun.machine, tRun.loaded,
      fun a h ↦ tRun.allocated a (lSaved.allocated a h), tRun.directionFlag,
      memoryWriteFrame_trans saved.frame (frame_mono frame (by
        intro r hr a ha
        exact ⟨Stack.region entry 2264, by simp, within_stack pre.call.stack sp r hr a ha⟩))⟩
  have mxcsr : t.MXCSR = s.MXCSR :=
    tMXCSR.trans ((lEffect.agrees.mxcsr (by simp [length_components])).trans
      (bEffect.mxcsr (by simp)))
  have fcw : t.FP87_Control = s.FP87_Control :=
    tFCW.trans ((lEffect.agrees.fcw (by simp [length_components])).trans
      (bEffect.fcw (by simp)))
  have updated : SavedFrame entry t boundary length := by
    apply saved.of_agreement global tSpS ?_ ?_ mxcsr fcw
    · exact agrees lo high frame (off := 488) (by decide) (by decide)
    · change memLoad t.external (stackPtr t + 224) 64 = memLoad s.external (stackPtr s + 224) 64
      rw [tSpS]
      exact agrees_memLoad (agrees lo high frame (off := 224) (size := 8) (by decide) (by decide))
  refine ⟨t, ⟨⟨_, execution⟩, updated, tRip, tSpS, ?_, ?_, ?_, ?_, ?_, ?_, counter, frame, ?_⟩⟩
  · exact (abi .rbx (by decide)).trans
      ((lEffect.agrees.read (n := 64) (r := 3) (by simp [length_components])).trans bRBX)
  · exact (abi .r14 (by decide)).trans
      ((lEffect.agrees.read (n := 64) (r := 14) (by simp [length_components])).trans bR14)
  · exact (abi .rbp (by decide)).trans
      ((lEffect.agrees.read (n := 64) (r := 5) (by simp [length_components])).trans bRBP)
  · exact (abi .r12 (by decide)).trans
      ((lEffect.agrees.read (n := 64) (r := 12) (by simp [length_components])).trans
        (bEffect.read (n := 64) (r := 12) (by simp)))
  · exact (abi .r13 (by decide)).trans (congrArg (· + 16) lSpS)
  · exact (abi .r15 (by decide)).trans (congrArg (· + 144) lSpS)
  · rw [tSP]
    exact tHash

end Hkdf.Proofs.NewExpand.Expand.Finalize.Inner
