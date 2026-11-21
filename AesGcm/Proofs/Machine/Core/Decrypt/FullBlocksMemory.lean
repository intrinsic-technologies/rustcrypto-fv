import AesGcm.Proofs.Machine.Core.Decrypt.FullBlocks

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem fullCtrMemory_stack_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hlow : 8 ≤ (args[4].get 64).toNat) (hhigh : (args[4].get 64).toNat + 48 ≤ 2^64) :
    RamWriteFrame (memStore mem (memLoad mem (args[4].get 64 + 64) 64 + 8)
      (((args[3].get 64 + ((16 : Nat) : BitVec 64)) &&& args[14].get 64) +
        memLoad mem (memLoad mem (args[4].get 64 + 64) 64 + 8) 64))
      (fullCtrMemory use256 args mem) [span (args[4].get 64 - 8) 56] := by
  let base := memStore mem (memLoad mem (args[4].get 64 + 64) 64 + 8)
      (((args[3].get 64 + ((16 : Nat) : BitVec 64)) &&& args[14].get 64) +
        memLoad mem (memLoad mem (args[4].get 64 + 64) 64 + 8) 64)
  change RamWriteFrame base (memStore (memStore (memStore (memStore
    (memStore base (args[4].get 64 + 16) (args[15].get 64))
    (args[4].get 64 + 24) (args[12].get 64))
    (args[4].get 64 + 32) (memLoad mem (memLoad mem (args[4].get 64 + 64) 64 + 8) 64))
    (args[4].get 64 + 40) (args[14].get 64 >>> 4))
    (args[4].get 64 - 8) (if use256 then (0x1028d0 : BitVec 64) else 0x102470)) _
  runtime_finish [span]

theorem fullCtrMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hlow : 8 ≤ (args[4].get 64).toNat) (hhigh : (args[4].get 64).toNat + 48 ≤ 2^64)
    (hdesc : (memLoad mem (args[4].get 64 + 64) 64 + 8).toNat + 8 ≤ 2^64) :
    RamWriteFrame mem (fullCtrMemory use256 args mem)
      [span (args[4].get 64 - 8) 56, span (memLoad mem (args[4].get 64 + 64) 64 + 8) 8] := by
  have initial : RamWriteFrame mem
      (memStore mem (memLoad mem (args[4].get 64 + 64) 64 + 8)
        (((args[3].get 64 + ((16 : Nat) : BitVec 64)) &&& args[14].get 64) +
          memLoad mem (memLoad mem (args[4].get 64 + 64) 64 + 8) 64))
      [span (args[4].get 64 - 8) 56, span (memLoad mem (args[4].get 64 + 64) 64 + 8) 8] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨span (memLoad mem (args[4].get 64 + 64) 64 + 8) 8, by simp, ?_⟩
    simp only [InRegion,span]
    omega
  apply initial.trans (fullCtrMemory_stack_frame use256 args mem hlow hhigh)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩

set_option maxHeartbeats 800000 in
theorem fullCtrMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (fullCtrMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x1028d0 else 0x102470) ∧
    memLoad (fullCtrMemory use256 args mem) (args[4].get 64 + 16) 64 = args[15].get 64 ∧
    memLoad (fullCtrMemory use256 args mem) (args[4].get 64 + 24) 64 = args[12].get 64 ∧
    memLoad (fullCtrMemory use256 args mem) (args[4].get 64 + 32) 64 =
      memLoad mem (memLoad mem (args[4].get 64 + 64) 64 + 8) 64 ∧
    memLoad (fullCtrMemory use256 args mem) (args[4].get 64 + 40) 64 = args[14].get 64 >>> 4 := by
  simp only [fullCtrMemory]
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
