import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Update.Layout
import Sha3.Proofs.LaneMemory

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem Initialized.stateAt {initial s : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode}
    (h : Initialized initial v mode s keccak fullState) :
    Update.StateAt (statePointer initial v mode keccak fullState) Incremental.initial s := by
  constructor
  · apply LaneMemory.memoryLanes_eq_of_bytes
    intro lane j
    simpa [storedByte, Incremental.initial] using h.zero (8 * lane.val + j.val) (by omega)
  · have hz : (Operand.mem (statePointer initial v mode keccak fullState + 200) : Operand 8).read s = 0 := by
      apply Bytes.memLoad (hn := by decide) (h128 := by decide)
      intro i hi
      have hi0 : i = 0 := by change i < 1 at hi; omega
      subst i
      simpa [storedByte] using h.zero 200 (by decide)
    change ((Operand.mem (statePointer initial v mode keccak fullState + 200) : Operand 8).read s).toNat = 0
    rw [hz]
    rfl

end Sha3.Proofs.Wrapper
