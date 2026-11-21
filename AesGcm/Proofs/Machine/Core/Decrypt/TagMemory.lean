import AesGcm.Proofs.Machine.Core.Decrypt.Calls

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem tagMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hlow : 8 ≤ (args[4].get 64).toNat)
    (hhigh : (args[4].get 64).toNat + 72 ≤ 2^64) :
    RamWriteFrame mem (tagMemory use256 args mem)
      [span (args[4].get 64 - 8) 16, span (args[4].get 64 + 64) 8] := by
  simp only [tagMemory]
  runtime_finish [span]

theorem tagMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (tagMemory use256 args mem) (args[4].get 64 + 64) 64 = args[15].get 64 ∧
    memLoad (tagMemory use256 args mem) (args[4].get 64) 64 = args[14].get 64 ∧
    memLoad (tagMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x1027e8 else 0x102388) := by
  simp only [tagMemory]
  repeat' apply And.intro
  all_goals
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (x := args[4].get 64)
            (by first | exact addr_sub _ _ | exact addr_self _ | rfl)
            (by first | exact addr_sub _ _ | exact addr_self _ | rfl)
          decide +kernel)]

end AesGcm.Proofs.Machine.Core.Decrypt
