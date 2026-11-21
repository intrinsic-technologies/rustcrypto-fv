import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Setup
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Fill
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256

theorem finish [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (input : FillReady initial s message v) :
    ∃ t, Padded initial t message v := by
  have tailBound : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨t, state, rip, rsp, zero, abi, frame⟩ := fill ctx input.toState input.rip input.rsp
    input.destination input.zero input.count (by omega)
  have preserved : Preserved initial t v := by
    apply Wrapper.preserved_of_bytes input.toPreserved state rsp
    rintro a ⟨i, hi, rfl⟩
    exact Wrapper.frame_bytes (offset := 176) (len := 24) ctx frame
      (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (.inr (by omega)) i hi
  have hashBytes : ∀ i < 32, t.external[stackPtr initial - 280 + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - 280 + BitVec.ofNat 64 i]? :=
    Wrapper.frame_bytes (offset := 280) (len := 32) ctx frame (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (.inr (by omega))
  have tailBytes : ∀ i < message.size % 64 + 1,
      t.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? :=
    Wrapper.frame_bytes (offset := 344) (len := message.size % 64 + 1) ctx frame (by omega) (by omega) (by decide) (by decide)
      (by decide) (by omega) (.inl (by omega))
  refine ⟨t, ⟨⟨preserved, Wrapper.hashState_of_bytes input.hashWords hashBytes,
    (abi.1 .r14 (by simp)).trans input.hashPointer⟩,
    (abi.1 .r12 (by simp)).trans input.blocks,
    (abi.1 .r15 (by simp)).trans input.tailLength⟩,
    rip, ?_, (abi.1 .rbx (by simp)).trans input.paddingLength⟩
  apply padded_bytes
  · refine ⟨input.tailBytes.1, ?_⟩
    intro i
    have hi : i.val < message.size % 64 := by simpa only [remainderBytes_size] using i.isLt
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 344).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, tailBytes i.val (by omega)]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.tailBytes.2 i
  · exact (tailBytes _ (by omega)).trans input.marker
  · intro i hi
    have byte := zero i hi
    have address : stackPtr initial - BitVec.ofNat 64 (280 + (63 - message.size % 64)) =
        stackPtr initial - 344 + BitVec.ofNat 64 (message.size % 64 + 1) := by
      have addr := Wrapper.stack_add input.rsp (offset := message.size % 64 + 1) (by omega)
      change stackPtr s + BitVec.ofNat 64 (message.size % 64 + 1) = _ at addr
      rw [input.rsp, show 344 - (message.size % 64 + 1) = 280 + (63 - message.size % 64) by omega] at addr
      exact addr.symm
    rw [address] at byte
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using byte

end Sha2.Proofs.Wrapper.Hash.Finalize.Pad
