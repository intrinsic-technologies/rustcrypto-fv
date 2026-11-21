import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.GHASHExecution.Evaluation
import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.GHASHExecution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

attribute [local irreducible] memStore memLoad bswapSpec

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem multiplyRam_frame (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (hRead : Readable mem (args[7].get 64) 32)
    (hStack : Readable mem (args[4].get 64 - 128) 136)
    (hRoom : 128 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (multiplyRam code args mem)
      [⟨(args[4].get 64 - 128).toNat, 128⟩, ⟨(args[7].get 64 + 16).toNat, 16⟩] := by
  generalize hbase : args[7].get 64 = base at *
  generalize hstack : args[4].get 64 = sp at *
  have hReadLow := hRead.low
  have hStackLow := hStack.low
  have hsp : (sp - 128).toNat = sp.toNat - 128 := by
    rw [BitVec.toNat_sub_of_le (by change 128 ≤ sp.toNat; exact hRoom)]
    rfl
  unfold multiplyRam
  extract_lets
  runtime_local_frame

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem multiplyRam_saved (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (hRead : Readable mem (args[7].get 64) 32)
    (hStack : Readable mem (args[4].get 64 - 128) 136)
    (hApart : (args[7].get 64).toNat + 32 ≤ (args[4].get 64 - 128).toNat ∨
      (args[4].get 64).toNat + 8 ≤ (args[7].get 64).toNat)
    (j : Fin 7) :
    memLoad (multiplyRam code args mem)
      (args[4].get 64 - BitVec.ofNat 64 (48 - 8 * j.val)) 64 =
      if j.val = 6 then memLoad mem (args[4].get 64) 64 else
        args[(match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) |>.get 64 := by
  generalize hbase : args[7].get 64 = base at *
  generalize hstack : args[4].get 64 = sp at *
  have hReadLow := hRead.low
  have hStackLow := hStack.low
  rcases j with ⟨j, hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold multiplyRam
     extract_lets
     simp only [Nat.reduceMul, Nat.reduceSub]
     runtime_local_memory_norm
     all_goals simp)

end AesGcm.Proofs.Machine.GHASHExecution
