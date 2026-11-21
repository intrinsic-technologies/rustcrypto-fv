import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Selection

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def coreMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (descriptorMemory args mem) (args[4].get 64 - 8)
    (if use256 then (0x1016e9 : BitVec 64) else 0x101409)

theorem coreMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hlow : (args[4].get 64).toNat + 56 < 2^64) :
    RamWriteFrame mem (coreMemory use256 args mem) [span (args[4].get 64 - 8) 64] := by
  simp only [coreMemory, descriptorMemory]
  runtime_finish [span]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem coreMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 32) 64 =
      selectedPointer (args[3].get 64) (args[5].get 64) (args[14].get 64) ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 40) 64 =
      selectedPointer (args[3].get 64) (args[5].get 64) (args[14].get 64) ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 + 48) 64 =
      selectedLength (args[3].get 64) (args[5].get 64) ∧
    memLoad (coreMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x1016e9 else 0x101409) := by
  simp only [coreMemory, descriptorMemory]
  repeat' apply And.intro
  all_goals
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (x := args[4].get 64)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
          decide)]

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
