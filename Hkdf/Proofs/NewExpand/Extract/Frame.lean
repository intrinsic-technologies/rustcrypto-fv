import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Saved.of_agrees {initial s t : RamState} (saved : Saved initial s)
    (same : (Component.mem (stackPtr initial - 48) 56).Agrees s t)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    Saved initial t := by
  have bound (slot : Syntax.Reg × Nat) (member : slot ∈ Encoding.Serialize.savedRegisters) :
      slot.2 ≤ 48 := by
    simp only [Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have slots := agrees_memLoad_slots same Encoding.Serialize.savedRegisters (48 - Prod.snd ·)
    (fun slot member ↦ by have := bound slot member; omega)
  have ret := agrees_memLoad_offset (width := 64) (offset := 48) same (by decide)
  refine ⟨?_, saved.returnAddress.trans ?_, mxcsr.trans saved.mxcsr, fcw.trans saved.fcw⟩
  · intro slot member
    have split : (48 : BitVec 64) =
        BitVec.ofNat 64 slot.2 + BitVec.ofNat 64 (48 - slot.2) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le (bound slot member)]
      rfl
    have word := slots slot member
    rw [split, ← BitVec.sub_sub, BitVec.sub_add_cancel] at word
    exact word.trans (saved.registers slot member)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] using ret.symm

theorem Frame.of_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {n : Nat} {regions : Vector MemoryRegion n}
    (stack : Stack.Valid initial 2264) (state : Frame initial s boundary)
    (running : Running initial boundary #v[Stack.region initial 2264] t)
    (frame : MemoryWriteFrame s t regions) (rsp : stackPtr t = stackPtr s)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control)
    (apart : ∀ written ∈ regions,
      (⟨(stackPtr initial - 48).toNat, 56⟩ : MemoryRegion).Disjoint written ∧
      (⟨(base initial + 80).toNat, 8⟩ : MemoryRegion).Disjoint written) :
    Frame initial t boundary := by
  have high := (stack_bounds stack).2
  have saves : (Component.mem (stackPtr initial - 48) 56).Agrees s t := by
    apply frame_agrees_of_disjoint frame
    · rw [show (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 from
        stack_sub_toNat stack (show 48 ≤ 2264 by decide)]
      omega
    · exact fun written member ↦ (apart written member).1
  have output : (Component.mem (base initial + 80) 8).Agrees s t := by
    apply frame_agrees_of_disjoint frame
    · have address : base initial + 80 = stackPtr initial - BitVec.ofNat 64 376 := by
        unfold base
        rw [show (456 : BitVec 64) = 376 + 80 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
        rfl
      rw [address, stack_sub_toNat stack (show 376 ≤ 2264 by decide)]
      omega
    · exact fun written member ↦ (apart written member).2
  exact ⟨running, state.toSaved.of_agrees saves mxcsr fcw, rsp.trans state.rsp,
    (agrees_memLoad output).trans state.outputPtr⟩

end Hkdf.Proofs.NewExpand.Extract
