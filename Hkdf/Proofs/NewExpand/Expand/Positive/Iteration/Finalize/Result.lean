import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def writes (sp : BitVec 64) : Vector MemoryRegion 3 :=
  #v[⟨sp.toNat - 344,344⟩, ⟨sp.toNat + 16,200⟩, ⟨sp.toNat + 256,8⟩]

structure Result [Bindings] (entry s t : RamState) (boundary : ReturnBoundary) (length : Nat)
    (key message : ByteArray) : Prop extends SavedFrame entry t boundary length where
  advances : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10f53c
  frameLocal : MemoryWriteFrame s t (writes (stackPtr s))
  r12Reg : t.regValue .r12 = s.regValue .r12
  r13Reg : t.regValue .r13 = stackPtr t + 16
  r14Reg : t.regValue .r14 = slot s 432
  chunk : t.regValue .rbx = slot s 264
  nextPtr : t.regValue .rbp = slot s 432 + slot s 264
  counter : slot t 256 = slot s 256 + 1
  digest : (⟨(stackPtr t + 16).toNat,32⟩ : MemoryRegion).HasBytes t.external
    (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message)

theorem agrees_local {entry s t : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) (frame : MemoryWriteFrame s t (writes (stackPtr s)))
    {offset len : Nat} (fit : offset + len ≤ 544)
    (work : offset + len ≤ 16 ∨ 216 ≤ offset) (counter : offset + len ≤ 256 ∨ 264 ≤ offset) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Agrees s t := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 :=
    (congrArg BitVec.toNat sp).trans (stack_sub_toNat stack (offset := 536) (by decide))
  obtain ⟨capacity, upper⟩ := stack_bounds stack
  have addr : (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  apply frame_agrees_of_disjoint frame (by rw [addr]; omega)
  intro r member a x y
  change _ ≤ a ∧ a < _ + len at x
  rw [addr] at x
  simp only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals dsimp only [MemoryRegion.Contains] at x y
  all_goals omega

theorem saved_of_frame [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {length : Nat}
    (saved : SavedFrame entry s boundary length) (stack : Stack.Valid entry 2264)
    (running : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t)
    (sp : stackPtr t = stackPtr s) (frame : MemoryWriteFrame s t (writes (stackPtr s)))
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    SavedFrame entry t boundary length := by
  apply saved.of_agreement running sp _ _ mxcsr fcw
  · exact agrees_local stack saved.sp frame (offset := 488) (len := 56) (by decide)
      (.inr (by decide)) (.inr (by decide))
  · change memLoad t.external (stackPtr t + 224) 64 = _
    rw [sp]
    exact agrees_memLoad (agrees_local stack saved.sp frame (offset := 224) (len := 8)
      (by decide) (.inr (by decide)) (.inl (by decide)))

theorem Result.slot_eq [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {length : Nat}
    {key message : ByteArray} (result : Result entry s t boundary length key message)
    (stack : Stack.Valid entry 2264) (original : stackPtr s = stackPtr entry - 536)
    (offset : Nat) (fit : offset ≤ 536) (work : offset + 8 ≤ 16 ∨ 216 ≤ offset)
    (counter : offset + 8 ≤ 256 ∨ 264 ≤ offset) :
    slot t (BitVec.ofNat 64 offset) = slot s (BitVec.ofNat 64 offset) := by
  change memLoad t.external (stackPtr t + _) 64 = _
  rw [show stackPtr t = stackPtr s from result.sp.trans original.symm]
  exact agrees_memLoad (agrees_local stack original result.frameLocal (by omega) work counter)

end Hkdf.Proofs.NewExpand.Expand.Finalize
