import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

def saveSixRegisters (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  memStore mem (sp - 48) (args[3].get 64)

theorem saveSixRegisters_frame (args : Values Value Reg.count) (mem : Ram)
    (hroom : 48 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (saveSixRegisters args mem) [span (args[4].get 64 - 48) 48] := by
  simp only [saveSixRegisters]
  runtime_finish [span]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem saveSixRegisters_loads (args : Values Value Reg.count) (mem : Ram) :
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 8) 64 = args[5].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (saveSixRegisters args mem) (args[4].get 64) 64 =
      memLoad mem (args[4].get 64) 64 := by
  simp only [saveSixRegisters]
  repeat' apply And.intro
  all_goals
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (x := args[4].get 64)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
            (by first | exact addr_sub _ _ | rfl | exact (BitVec.add_zero _).symm)
          decide)]


theorem saveSixRegisters_call_loads (args : Values Value Reg.count) (mem : Ram)
    (slot ret : BitVec 64)
    (hapart : RangeApart slot 8 (args[4].get 64 - 48) 56) :
    let saved := memStore (saveSixRegisters args mem) slot ret
    memLoad saved (args[4].get 64 - 8) 64 = args[5].get 64 ∧
    memLoad saved (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad saved (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad saved (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad saved (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad saved (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad saved (args[4].get 64) 64 = memLoad mem (args[4].get 64) 64 ∧
    memLoad saved slot 64 = ret := by
  have hload (off : Nat) (hoff : off ≤ 48) :
      memLoad (memStore (saveSixRegisters args mem) slot ret)
        (args[4].get 64 - BitVec.ofNat 64 off) 64 =
      memLoad (saveSixRegisters args mem) (args[4].get 64 - BitVec.ofNat 64 off) 64 := by
    apply memLoad_memStore_of_rangeApart
    have hp := X86Proofs.Refine.RangeApart.right_sub hapart (off := 48 - off) (m' := 8) (by omega)
    have he : args[4].get 64 - (48 : BitVec 64) + BitVec.ofNat 64 (48 - off) =
        args[4].get 64 - BitVec.ofNat 64 off := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 48 off (by omega) (by omega)]
      bv_omega
    rwa [he] at hp
  obtain ⟨h8, h16, h24, h32, h40, h48, h0⟩ := saveSixRegisters_loads args mem
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hload 8 (by decide)).trans h8
  · exact (hload 16 (by decide)).trans h16
  · exact (hload 24 (by decide)).trans h24
  · exact (hload 32 (by decide)).trans h32
  · exact (hload 40 (by decide)).trans h40
  · exact (hload 48 (by decide)).trans h48
  · have hp := hload 0 (by decide)
    simp only [BitVec.sub_zero] at hp
    exact hp.trans h0
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end AesGcm.Proofs.Machine.Runtime
