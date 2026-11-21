import Sha2.Proofs.Common.SHA512.Compression.Execution
import Sha2.Proofs.Common.SHA512.Compression.Interface
import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem registers_of_obs {s t : RamState} {hash : Array UInt64}
    (h : Obs s t) (registers : RegistersAt s hash) : RegistersAt t hash := by
  refine ⟨registers.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.read_reg (n := 64) 11).symm.trans registers.a
  · exact (h.read_reg (n := 64) 1).symm.trans registers.b
  · exact (h.read_reg (n := 64) 10).symm.trans registers.c
  · exact (h.read_reg (n := 64) 0).symm.trans registers.d
  · exact (h.read_reg (n := 64) 3).symm.trans registers.e
  · exact (h.read_reg (n := 64) 9).symm.trans registers.f
  · exact (h.read_reg (n := 64) 8).symm.trans registers.g
  · exact (h.read_reg (n := 64) 13).symm.trans registers.h

theorem blockComponents_preserves_slot {s t : RamState}
    (frame : AgreesExcept (blockComponents s) s t) {offset : Nat}
    (ho : offset = 224 ∨ offset = 232) :
    memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
  apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees frame
  intro i hi c hc ha
  simp only [blockComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 0) (b := offset) (len := 224)
      (count := 8) (by omega) (by omega) (Or.inl (by omega)) j hj i hi
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 240) (b := offset) (len := 128)
      (count := 8) (by omega) (by omega) (Or.inr (by omega)) j hj i hi
    simpa only [BitVec.ofNat_eq_ofNat] using he.symm

theorem block_result_of_trace [Bindings]
    (instructions : List CheckedInstruction) (s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt64) (block : ByteArray) (code : CodeMap)
    (ready : ReadyToStep s) (loaded : CodeIn code s)
    (safe : InstructionTrace.Safe s code boundary instructions s)
    (rip : (InstructionTrace.run instructions s).RIP = 0x111802)
    (rsi : (InstructionTrace.run instructions s).regValue .rsi = s.regValue .rsi)
    (registers : RegistersAt (InstructionTrace.run instructions s)
      (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits block)))
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
    registers_of_obs obs registers, finalFrame, ?_, ?_⟩⟩
  · rw [rsp]
    exact blockComponents_preserves_slot finalFrame (by decide)
  · rw [rsp]
    exact blockComponents_preserves_slot finalFrame (by decide)

end Sha2.Proofs.Common.SHA512.Compression
