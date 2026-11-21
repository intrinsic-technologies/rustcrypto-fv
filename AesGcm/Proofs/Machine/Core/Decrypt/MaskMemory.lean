import AesGcm.Proofs.Machine.Core.Decrypt.Calls

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem maskMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hlow : 8 ≤ (args[4].get 64).toNat)
    (hhigh : (args[4].get 64).toNat + 136 ≤ 2^64) :
    RamWriteFrame mem (maskMemory use256 args mem) [span (args[4].get 64 - 8) 144] := by
  simp only [maskMemory]
  runtime_finish [span]

set_option maxHeartbeats 800000 in
theorem maskMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hapart : RangeApart (args[4].get 64 + 80) 8 (args[6].get 64 + 8) 4) :
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 16) 32 =
      memLoad mem (args[6].get 64) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 20) 32 =
      memLoad mem (args[6].get 64 + 4) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 24) 32 =
      memLoad mem (args[6].get 64 + 8) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 28) 32 = 0x1000000 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 60) 32 =
      memLoad mem (args[6].get 64) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 56) 32 =
      memLoad mem (args[6].get 64 + 4) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 52) 32 =
      memLoad mem (args[6].get 64 + 8) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 72) 64 = args[7].get 64 + 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 80) 64 = args[2].get 64 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x1027bc else 0x10235c) := by
  have hw2 : memLoad (memStore mem (args[4].get 64 + 80) (args[2].get 64))
      (args[6].get 64 + 8) 32 = memLoad mem (args[6].get 64 + 8) 32 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ hapart
  simp only [maskMemory, hw2]
  repeat' apply And.intro
  all_goals
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (x := args[4].get 64)
            (by first | exact addr_sub _ _ | rfl)
            (by first | exact addr_sub _ _ | rfl)
          decide +kernel)]

end AesGcm.Proofs.Machine.Core.Decrypt
