import Sha3.Proofs.Wrapper.Finish.Code
import Sha3.Proofs.Wrapper.Frame

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem epilogueSlot_frame (initial : RamState) (v : Variant) (mode : Mode) (k : Nat)
    (keccak : Bool := false) (fullState : Bool := false) :
    epilogueSlot initial k mode fullState = frameBase initial v mode keccak fullState +
      BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - 8 * mode.pushCount fullState + 8 * k) := by
  have hle : 8 * mode.pushCount fullState ≤ mode.frameSize v keccak fullState := by
    cases mode <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  have he : BitVec.ofNat 64 (mode.frameSize v keccak fullState) =
      BitVec.ofNat 64 (8 * mode.pushCount fullState) +
        BitVec.ofNat 64 (mode.frameSize v keccak fullState - 8 * mode.pushCount fullState) := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  unfold epilogueSlot frameBase
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, he, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem returnFromEpilogue [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hRip : s.RIP = epilogueAddress mode v keccak fullState) (hRsp : stackPtr s = frameBase initial v mode keccak fullState)
    (hPreserved : ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount fullState),
        (epiloguePopReg mode fullState i).setWidth 5 ≠
          (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j]) :
    ∃ final, Returns (returnBoundary initial) (mode.pushCount fullState + 2) s final ∧ Invariant initial v mode final keccak fullState ∧
      final.external = s.external ∧ CalleeSavedRegistersUnchanged initial final := by
  have hBounds := validInvocation_returnBoundary_bounds hInitial hCall
  have hPre : EpiloguePre v (epilogueAddress mode v keccak fullState) initial mode s keccak fullState := by
    refine ⟨hRip, hRsp, hSaved, ?_, hBounds.1, hPreserved⟩
    intro i
    rw [epilogueSlot_frame initial v mode i.val keccak fullState]
    apply hInv.frameReadable hCall.stackAvailable
    have := i.isLt
    have hm : 8 * mode.pushCount fullState ≤ (mode.frameSize v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
    omega
  obtain ⟨t, hReturn, hReady, hResult⟩ := epilogue_returns v mode (epilogueAddress mode v keccak fullState) initial keccak fullState
    (epilogueCode_subset mode v keccak fullState) (fun k hk he ↦
      hBounds.2 (he ▸ epiloguePop_inProgram mode v k keccak fullState hk)) s hInv.ready hInv.code hPre
  exact ⟨t, hReturn, hInv.of_agreesExcept hCall hReady hResult.agrees
    (epilogueChanges_writesWithin _), hResult.memory, hResult.saved⟩

end Sha3.Proofs.Wrapper.Finish
