import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Call

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def localRegions (sp : BitVec 64) (offset bytes depth : Nat) : Vector MemoryRegion 2 :=
  #v[⟨(sp + BitVec.ofNat 64 offset).toNat, bytes⟩, ⟨sp.toNat - depth, depth⟩]

abbrev longRegions (s : RamState) := localRegions (stackPtr s) 272 104 344

theorem workBounds [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {length : Nat}
    (stack : Stack.Valid entry 2264) (frame : SavedFrame entry s boundary length) :
    344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 544 < 2^32 := by
  have sp : stackPtr s = stackPtr entry - BitVec.ofNat 64 536 := frame.sp
  rw [sp, stack_sub_toNat stack (by decide)]
  have := stack_bounds stack
  omega

theorem offset_toNat {sp : BitVec 64} {offset : Nat}
    (bound : sp.toNat + 544 < 2^32) (fits : offset ≤ 544) :
    (sp + BitVec.ofNat 64 offset).toNat = sp.toNat + offset := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
    Nat.mod_eq_of_lt (by omega)]

private theorem contains_local {sp : BitVec 64} {offset bytes depth a : Nat}
    (h : sp.toNat + 544 < 2^32) (fit : offset ≤ 544) (below : depth ≤ sp.toNat) :
    (∃ r ∈ localRegions sp offset bytes depth, r.Contains a) ↔
      (sp.toNat + offset ≤ a ∧ a < sp.toNat + offset + bytes) ∨
      (sp.toNat - depth ≤ a ∧ a < sp.toNat) := by
  simp [localRegions, MemoryRegion.Contains, offset_toNat h fit, Nat.sub_add_cancel below]

theorem widenLocal {s t : RamState} {sp : BitVec 64} {off n d off' n' d' : Nat}
    (bounds : 344 ≤ sp.toNat ∧ sp.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (localRegions sp off n d))
    (lo : off' ≤ off) (hi : off + n ≤ off' + n') (depth : d ≤ d')
    (width : off' + n' ≤ 544) (below : d' ≤ 344) :
    MemoryWriteFrame s t (localRegions sp off' n' d') := by
  apply frame_mono frame
  intro r hr a ha
  have h := (contains_local bounds.2 (by omega) (by omega)).mp ⟨r, hr, ha⟩
  apply (contains_local bounds.2 (by omega) (by omega)).mpr
  rcases h with h|h
  · left; omega
  · right; omega

theorem localAgrees {s t : RamState} {sp : BitVec 64} {off n d keep size : Nat}
    (bounds : 344 ≤ sp.toNat ∧ sp.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (localRegions sp off n d))
    (within : off + n ≤ 544) (below : d ≤ 344) (fits : keep + size ≤ 544)
    (apart : keep + size ≤ off ∨ off + n ≤ keep) :
    (Component.mem (sp + BitVec.ofNat 64 keep) size).Agrees s t := by
  apply frame_agrees_of_disjoint frame
  · rw [offset_toNat bounds.2 (by omega)]
    omega
  · intro r hr a ha hb
    have h := (contains_local bounds.2 (by omega) (by omega)).mp ⟨r, hr, hb⟩
    change (sp + BitVec.ofNat 64 keep).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 keep).toNat + size at ha
    rw [offset_toNat bounds.2 (by omega)] at ha
    omega

theorem savedOfLocal [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length fuel : Nat} {cs : List Component}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t) (ag : AgreesExcept cs s t)
    (writes : WritesWithin cs (longRegions s))
    (preserved : .reg 4 ∉ cs ∧ .df ∉ cs ∧ .mxcsr ∉ cs ∧ .fcw ∉ cs) :
    SavedFrame entry t boundary length := by
  have bounds := workBounds pre.call.stack saved
  have sp : stackPtr s = stackPtr entry - BitVec.ofNat 64 536 := saved.sp
  have spNat := congrArg BitVec.toNat sp
  rw [stack_sub_toNat pre.call.stack (by decide)] at spNat
  have localFrame := ag.memoryWriteFrame writes
  have running := saved.toRunning.of_agrees run ready ag (by
    intro c hc a ha
    obtain ⟨r, hr, inside⟩ := writes c hc a ha
    have ha := (contains_local bounds.2 (by decide : 272 ≤ 544) (by omega : 344 ≤ (stackPtr s).toNat)).mp
      ⟨r, hr, inside⟩
    refine ⟨Stack.region entry 2264, by simp, ?_⟩
    change (Stack.region entry 2264).start ≤ _ ∧ _ < (Stack.region entry 2264).start + _
    rw [stack_region_end]
    change (stackPtr entry).toNat - 2264 ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8
    have := stack_bounds pre.call.stack
    omega) (by
      simp only [writtenLength, limit, ↓reduceIte]
      intro r hr a ha h
      exact ((pre.separation pos limit).2 r hr).2 a ha (.inl h)) preserved.2.1
  have spT : t.regValue .rsp = s.regValue .rsp := ag.read (n := 64) (r := 4) preserved.1
  apply saved.of_agreement running spT
  · exact localAgrees bounds localFrame (by decide) (by decide) (by decide) (by decide)
  · unfold slot
    rw [spT]
    exact agrees_memLoad (localAgrees bounds localFrame (keep := 224) (size := 8)
      (by decide) (by decide) (by decide) (by decide))
  · exact ag.mxcsr preserved.2.2.1
  · exact ag.fcw preserved.2.2.2

theorem writesLocal {sp : BitVec 64} {off n d : Nat} {cs : List Component}
    (bounds : 344 ≤ sp.toNat ∧ sp.toNat + 544 < 2^32) (fits : off + n ≤ 544)
    (below : d ≤ 344)
    (covered : ∀ c ∈ cs, ∀ a, c.Covers a → (Component.mem (sp + BitVec.ofNat 64 off) n).Covers a) :
    WritesWithin cs (localRegions sp off n d) := by
  intro c hc a ha
  obtain ⟨i, hi, eq⟩ := covered c hc a ha
  apply (contains_local bounds.2 (by omega) (by omega)).mpr
  left
  subst a
  rw [BitVec.toNat_add, offset_toNat bounds.2 (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
  omega

theorem copyLocalFrame {s t : RamState} {offset count : Nat}
    (bounds : 344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 544 < 2^32)
    (dest : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 offset)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi count, ⟨(stackPtr s - 8).toNat, 8⟩]) :
    MemoryWriteFrame s t (localRegions (stackPtr s) offset count 8) := by
  have depth : (stackPtr s - 8).toNat = (stackPtr s).toNat - 8 := by
    apply BitVec.toNat_sub_of_le
    change 8 ≤ (stackPtr s).toNat
    omega
  simpa only [localRegions, registerRegion, dest, depth] using frame

theorem savedOfStore [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length fuel off n : Nat} {cs : List Component}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t) (ag : AgreesExcept cs s t)
    (lo : 272 ≤ off) (hi : off + n ≤ 376)
    (covered : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 off) n).Covers a)
    (preserved : .reg 4 ∉ cs ∧ .df ∉ cs ∧ .mxcsr ∉ cs ∧ .fcw ∉ cs) :
    SavedFrame entry t boundary length ∧ MemoryWriteFrame s t (localRegions (stackPtr s) off n 0) := by
  have bounds := workBounds pre.call.stack saved
  have small := writesLocal bounds (d := 0) (by omega) (by decide) covered
  refine ⟨savedOfLocal pre pos limit saved run ready ag (fun c hc a covered ↦ ?_) preserved,
    ag.memoryWriteFrame small⟩
  have h := (contains_local bounds.2 (by omega) (Nat.zero_le _)).mp (small c hc a covered)
  apply (contains_local bounds.2 (by decide : 272 ≤ 544) bounds.1).mpr
  omega

end Hkdf.Proofs.NewExpand.Expand.Info
