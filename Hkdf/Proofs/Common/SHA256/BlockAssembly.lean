import Hkdf.Proofs.Common.SHA256.Compression.Execution
import Hkdf.Proofs.Common.SHA256.Compression.Interface
import Hkdf.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Compression

theorem RegistersAt.of_obs {s t : RamState} {hash : Array UInt32}
    (h : Obs s t) (registers : RegistersAt s hash) : RegistersAt t hash := by
  refine ⟨registers.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.read_reg (n := 32) 3).symm.trans registers.a
  · exact (h.read_reg (n := 32) 14).symm.trans registers.b
  · exact (h.read_reg (n := 32) 0).symm.trans registers.c
  · exact (h.read_reg (n := 32) 9).symm.trans registers.d
  · exact (h.read_reg (n := 32) 8).symm.trans registers.e
  · exact (h.read_reg (n := 32) 10).symm.trans registers.f
  · exact (h.read_reg (n := 32) 2).symm.trans registers.g
  · exact (h.read_reg (n := 32) 1).symm.trans registers.h

theorem blockComponents_preserves_slot {s t : RamState}
    (frame : AgreesExcept (blockComponents s) s t) {offset : Nat}
    (lo : 192 ≤ offset) (hi : offset + 8 ≤ 208) :
    memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
  apply Hkdf.Proofs.Common.Encoding.Serialize.read_mem_of_agrees frame
  intro i hi' c hc ha
  simp only [blockComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 0) (b := offset) (len := 192) (count := 8)
      (by omega) (by omega) (Or.inl (by omega)) j hj i hi'
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm
  · obtain ⟨j, hj, he⟩ := ha
    exact RangeApart.offsets (stackPtr s) (a := 208) (b := offset) (len := 80) (count := 8)
      (by omega) (by omega) (Or.inr (by omega)) j hj i hi' he.symm

theorem block_result_of_trace [Bindings]
    (instructions : List CheckedInstruction) (s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (block : ByteArray) (code : CodeMap)
    (ready : ReadyToStep s) (loaded : CodeIn code s)
    (safe : InstructionTrace.Safe s code boundary instructions s)
    (rip : (InstructionTrace.run instructions s).RIP = 0x10bd92)
    (rsi : (InstructionTrace.run instructions s).regValue .rsi = s.regValue .rsi)
    (registers : RegistersAt (InstructionTrace.run instructions s)
      (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits block)))
    (frame : ∀ actual final, AgreesExcept (InstructionTrace.components instructions s) actual final →
      AgreesExcept (blockComponents s) actual final) :
    ∃ t, BlockResult s t boundary hash block := by
  obtain ⟨fuel, t, execution, finalReady, _, obs, finalRip, agrees⟩ :=
    InstructionTrace.execute instructions s s s code boundary ready loaded
      (Obs.refl s) rfl (fun _ h => h) safe
  have finalFrame := frame s t agrees
  have rsp : stackPtr t = stackPtr s := finalFrame.read (n := 64) (r := 4)
    (by simp [blockComponents])
  refine ⟨t, ⟨⟨fuel, execution⟩, finalReady, finalRip.symm.trans rip, rsp,
    (obs.read_reg (n := 64) 6).symm.trans rsi,
    registers.of_obs obs, finalFrame, ?_, ?_⟩⟩
  · rw [rsp]
    exact blockComponents_preserves_slot finalFrame (offset := 192) (by decide) (by decide)
  · rw [rsp]
    exact blockComponents_preserves_slot finalFrame (offset := 200) (by decide) (by decide)

end Hkdf.Proofs.Common.SHA256
