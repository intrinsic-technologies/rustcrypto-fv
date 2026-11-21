import Sha3.Proofs.Update.Layout

namespace Sha3.Proofs.Update

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program

theorem CallContext.input_size_lt [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state) :
    bytes.size < 2 ^ 32 := by
  have hinput := h.inputRead.low
  have hstate := h.stateRead.low
  by_cases hn : bytes.size < 2 ^ 32
  · exact hn
  exfalso
  have hsize : bytes.size = 2 ^ 32 := by omega
  have hbase : (initial.regValue .rdx).toNat = 0 := by omega
  apply h.inputApart (stateRegion initial) (by simp [writeRegions])
    (initial.regValue .rsi).toNat
  · simp only [MemoryRegion.Contains, hbase, hsize, Nat.zero_add]
    exact ⟨Nat.zero_le _, by omega⟩
  · simp [stateRegion, MemoryRegion.Contains]

end Sha3.Proofs.Update
