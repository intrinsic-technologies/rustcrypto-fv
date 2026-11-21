import P256.Proofs.Nonce.UpdateValue.Prepare.Key.Setup
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Key

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem arguments [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (saved : Saved initial s state) : Setup.Pre s := by
  refine ⟨saved.rip, ?_, ?_, ?_, ?_⟩
  · intro off bound aligned
    rw [ScalarFrame.scalar_stack_address (frameOffset := 488) saved.rsp (by decide) (by omega)]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)) saved.allocated
  · intro off bound
    rw [saved.statePointer]
    have address : (initial.regValue .rdi + BitVec.ofNat 64 off).toNat = (initial.regValue .rdi).toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64)]
      exact Nat.mod_eq_of_lt (by have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded; omega)
    refine ⟨?_, ?_⟩
    · rw [address]
      have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
      omega
    · intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact saved.allocated _ (Option.isSome_iff_exists.mpr (pre.stateAllocated _
        (memoryRegion_contains_add (len := 64) pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega))))
  · intro off bound j span i hi k hk he
    rw [saved.statePointer] at he
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at he
    apply pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : j+k<64))
    rw [← he]
    apply work_substack pre
    apply work_contains_scratch pre bound
    exact ⟨i, hi, by rw [show stackPtr s = scratch initial from saved.rsp, BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  · intro off len bound codeOffset codeLen codeBound
    exact ScalarFrame.stack_code (frameOffset := 488) pre.callee saved.toFrameState (by decide) (by omega) codeBound

end P256.Proofs.Nonce.UpdateValue.Prepare.Key
