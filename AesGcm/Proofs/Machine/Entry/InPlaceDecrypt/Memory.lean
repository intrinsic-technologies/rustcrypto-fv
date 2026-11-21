import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Blocks
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.CoreCall
import AesGcm.Proofs.Machine.Runtime.SavedRegisters
import AesGcm.Proofs.Common.Tagged
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Region

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem entryMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : (if use256 then 592 else 464) ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory use256 args mem)
      [span (args[4].get 64 - (if use256 then 592 else 464))
        (if use256 then 592 else 464)] := by
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hroom ⊢
  all_goals simp only [entryMemory, Bool.false_eq_true, ↓reduceIte]
  all_goals runtime_finish [span]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem entryMemory_saved (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 8) 64 = args[5].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (entryMemory use256 args mem)
      (args[4].get 64 - (if use256 then 592 else 464)) 64 =
      (if use256 then 0x101550 else 0x101270) := by
  have hapart : RangeApart (args[4].get 64 - (if use256 then 592 else 464)) 8
      (args[4].get 64 - 48) 56 := by
    cases use256
    all_goals
      apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
      decide +kernel
  obtain ⟨h8, h16, h24, h32, h40, h48, _, hret⟩ :=
    saveSixRegisters_call_loads args mem
      (args[4].get 64 - (if use256 then 592 else 464))
      (if use256 then 0x101550 else 0x101270) hapart
  exact ⟨h8, h16, h24, h32, h40, h48, hret⟩

theorem coreMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat) (hlow : (args[4].get 64).toNat + 40 < 2^64) :
    RamWriteFrame mem (coreMemory use256 args mem) [span (args[4].get 64 - 8) 48] := by
  simp only [coreMemory]
  runtime_finish [span]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem coreMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (coreMemory use256 args mem) (args[4].get 64) 64 =
      memLoad mem (args[12].get 64 + args[13].get 64 - 16) 64 ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 8) 64 =
      memLoad mem (args[12].get 64 + args[13].get 64 - 8) 64 ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 16) 64 = args[12].get 64 ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 24) 64 = args[12].get 64 ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 32) 64 = args[13].get 64 - 16 ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x1015af else 0x1012cf) := by
  simp only [coreMemory]
  repeat' apply And.intro
  all_goals
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (x := args[4].get 64)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
          decide)]

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
