import P256.Proofs.Nonce.Update.Seeded.Prepare.KeySetup
import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

set_option maxRecDepth 2048 in
theorem key_call_entry [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {original state : State}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : KeyReady initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (KeySetup.effect s).Holds s t := by
  have hp : KeySetup.Pre s := by
    refine ⟨input.rip, ?_, ?_, ?_, ?_⟩
    · intro off member
      have bound : off + 8 ≤ 32 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      rw [show (Operand.reg 3 : Operand 64).read s = initial.regValue .rdi from input.drbgPointer]
      have address : (initial.regValue .rdi + BitVec.ofNat 64 off).toNat = (initial.regValue .rdi).toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64)]
        exact Nat.mod_eq_of_lt (by have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded; omega)
      refine ⟨?_, ?_⟩
      · rw [address]
        have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
        omega
      · intro i hi
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact input.allocated _ (Option.isSome_iff_exists.mpr (pre.stateAllocated _
          (memoryRegion_contains_add (len := 64) pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega))))
    · intro off member
      have bound : off ≤ 632 ∧ (680-off)%8=0 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [show rspOf s = stackPtr s from rfl,
        ScalarFrame.scalar_stack_address (frameOffset := 680) input.rsp (by decide) (by omega)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) bound.2) input.allocated
    · intro off member codeOffset codeLen codeBound
      have bound : off + 8 ≤ 632 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      exact ScalarFrame.stack_code (frameOffset := 680) pre.callee input.toFrameState (by decide) (by omega) codeBound
    · intro off member i hi j hj he
      have bound : off + 8 ≤ 632 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      rw [show (Operand.reg 3 : Operand 64).read s = initial.regValue .rdi from input.drbgPointer] at he
      apply pre.separation _ (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : j<64))
      rw [← he]
      apply Update.Prepare.work_substack pre
      apply Update.Prepare.work_contains_scratch pre bound
      exact ⟨i, hi, by rw [show rspOf s = scratch initial from input.rsp]⟩
  obtain ⟨fuel,t,run,ready,_,holds⟩ := KeySetup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0xa455 KeySetup.bytes (by decide) (by decide +kernel)) hp
  exact ⟨fuel,t,run,ready,holds⟩

end P256.Proofs.Nonce.Update.Seeded.Prepare
