import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info.Short

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def footprint (sp : BitVec 64) (previous count : Nat) : Vector MemoryRegion 3 :=
  #v[⟨(sp + 272 + BitVec.ofNat 64 previous).toNat, count⟩,
     ⟨(sp - 8).toNat, 8⟩, ⟨(sp + 335).toNat, 1⟩]

theorem untouched {s t : RamState} {sp : BitVec 64} {previous count offset : Nat}
    (frame : MemoryWriteFrame s t (footprint sp previous count))
    (low : 8 ≤ sp.toNat) (high : sp.toNat + 544 < 2^64)
    (short : previous + count < 64) (fits : offset < 544)
    (copy : offset < 272 + previous ∨ 272 + previous + count ≤ offset)
    (index : offset ≠ 335) :
    t.external[sp + BitVec.ofNat 64 offset]? = s.external[sp + BitVec.ofNat 64 offset]? := by
  apply frame
  intro r hr hrange
  unfold footprint at hr
  have cases : r = ⟨(sp + 272 + BitVec.ofNat 64 previous).toNat, count⟩ ∨
      r = ⟨(sp - 8).toNat, 8⟩ ∨ r = ⟨(sp + 335).toNat, 1⟩ := by simpa using hr
  rcases cases with rfl | rfl | rfl <;>
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.reduceToNat] at hrange <;> omega

theorem slot_eq {s t : RamState} {previous count off : Nat}
    (frame : MemoryWriteFrame s t (footprint (stackPtr s) previous count))
    (sp : stackPtr t = stackPtr s) (low : 8 ≤ (stackPtr s).toNat)
    (high : (stackPtr s).toNat + 544 < 2^64) (short : previous + count < 64)
    (fits : off + 8 ≤ 544)
    (copy : off + 8 ≤ 272 + previous ∨ 272 + previous + count ≤ off)
    (index : off + 8 ≤ 335 ∨ 335 < off) :
    slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
  change memLoad t.external (stackPtr t + _) 64 = memLoad s.external (stackPtr s + _) 64
  rw [sp]
  apply agrees_memLoad
  intro i hi
  change i < 8 at hi
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    untouched (offset := off + i) frame low high short (by omega) (by omega) (by omega)

theorem savedFrame {entry s t : RamState} {boundary : ReturnBoundary} {length previous count : Nat}
    [Bindings] (saved : SavedFrame entry s boundary length) (stack : Stack.Valid entry 2264)
    (running : Running entry boundary #v[registerRegion entry .rcx (writtenLength length),
        Stack.region entry 2264] t)
    (sp : stackPtr t = stackPtr s) (short : previous + count < 64)
    (frame : MemoryWriteFrame s t (footprint (stackPtr s) previous count))
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    SavedFrame entry t boundary length := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    exact stack_sub_toNat stack (offset := 536) (by decide)
  have bounds := stack_bounds stack
  have same (off : Nat) (fit : off < 544) (copy : off < 272 + previous ∨
      272 + previous + count ≤ off) (index : off ≠ 335) :=
    untouched frame (by omega) (by omega) short fit copy index
  apply saved.of_agreement running sp ?_ ?_ mxcsr fcw
  · intro i hi
    simpa only [stackPtr_eq_regValue_rsp, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      same (488+i) (by omega) (.inr (by omega)) (by omega)
  · exact slot_eq (off := 224) frame sp (by omega) (by omega) short (by decide)
      (.inl (by omega)) (.inl (by decide))

end Hkdf.Proofs.NewExpand.Expand.Info.Short
