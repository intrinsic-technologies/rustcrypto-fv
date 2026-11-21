import Sha3.Proofs.Wrapper.Finish.Code
import Sha3.Proofs.Wrapper.Finish.Call
import Sha3.Proofs.Wrapper.Reset.Selection
import X86Proofs.Instructions.MovLoad.Triple

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def argumentChanges : List Component := [.reg 6, .reg 7, .rip]

theorem argumentChanges_noMem : ∀ c ∈ argumentChanges, ∀ address, ¬ c.Covers address := by
  simp [argumentChanges, Component.Covers]

def outputOperand (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : Operand 64 :=
  match mode with
  | .digest => .reg 3
  | _ => .mem (outputSlot initial v mode keccak fullState)

theorem argumentLea_image (v : Variant) (keccak fullState : Bool := false) :
    ImageAt (startAddress .reset v keccak fullState) [0x48, 0x8d, 0x7c, 0x24, 0x08] := by
  unfold ImageAt
  cases keccak <;> cases fullState <;> cases v <;> decide +kernel

theorem argumentOutput_reset_image (v : Variant) (keccak fullState : Bool := false) :
    ImageAt (startAddress .reset v keccak fullState + 5) [0x48, 0x8b, 0x34, 0x24] := by
  unfold ImageAt
  cases keccak <;> cases fullState <;> cases v <;> decide +kernel

theorem arguments_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hCall : ValidInvocation bindings v .reset initial inputs split keccak fullState)
    (hInv : Invariant initial v .reset s keccak fullState)
    (hRip : s.RIP = startAddress .reset v keccak fullState) (hRsp : stackPtr s = frameBase initial v .reset keccak fullState)
    (hOutput : (outputOperand initial v .reset keccak fullState).read s = out) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ Invariant initial v .reset t keccak fullState ∧
      t.RIP = callAddress .reset v keccak fullState ∧ stackPtr t = frameBase initial v .reset keccak fullState ∧
      t.regValue .rdi = statePointer initial v .reset keccak fullState ∧ t.regValue .rsi = out ∧
      t.external = s.external ∧ AgreesExcept argumentChanges s t := by
  have hNe : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hRsp, frameBase]
    apply stackSub_ne_returnBoundary
    cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  have hLea := lea_r64_effect_step (startAddress .reset v keccak fullState) 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨u, hRunU, hInvU, hNeU, hEffectU, hFrameU⟩ := Reset.advanceNoMemory hCall hLea
    (argumentLea_image v keccak fullState) (changes := argumentChanges)
    (by change ∀ c ∈ [Component.reg 7, .rip], c ∈ argumentChanges
        simp [argumentChanges]) argumentChanges_noMem (by decide)
    hInv hNe hRip
  have hMemU := hFrameU.external argumentChanges_noMem
  have hRspU : stackPtr u = frameBase initial v .reset keccak fullState :=
    (hFrameU.read (n := 64) (r := 4) (by decide)).trans hRsp
  have hStateU : u.regValue .rdi = statePointer initial v .reset keccak fullState := by
    have he : u.regValue .rdi = stackPtr s + 8 := hEffectU.writes
    rw [he, hRsp]
    cases keccak <;> cases fullState <;> cases v <;> rfl
  have hOutU : (outputOperand initial v .reset keccak fullState).read u = out := by
    simpa only [outputOperand, Operand.read, hMemU] using hOutput
  have hFinish : ∃ t, Advances (returnBoundary initial) 1 u t ∧ Invariant initial v .reset t keccak fullState ∧
      t.RIP = callAddress .reset v keccak fullState ∧ t.regValue .rsi = out ∧
      AgreesExcept [.reg 6, .rip] u t := by
    have hMov := mov_r64_m64_effect_step (startAddress .reset v keccak fullState + 5) 0x48
      (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 .none) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    have hRead : MemReadable u (stackPtr u) 8 := by
      rw [hRspU]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (hInvU.frameReadable hCall.stackAvailable (offset := 0) (count := 8) (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel))
    obtain ⟨t, hr, hi, _, he, hf⟩ := Reset.advanceNoMemory hCall hMov
      (argumentOutput_reset_image v keccak fullState) (changes := [.reg 6, .rip])
      (by change ∀ c ∈ [Component.reg 6, .rip], c ∈ [Component.reg 6, .rip]
          exact fun _ h ↦ h)
      (by simp [Component.Covers]) (by decide) hInvU hNeU ⟨hEffectU.rip, by
        change MemReadable u (stackPtr u + 0) 8
        rw [show stackPtr u + 0 = stackPtr u from BitVec.add_zero _]
        exact hRead⟩
    refine ⟨t, hr, hi, he.rip.trans (by cases keccak <;> cases fullState <;> cases v <;> rfl), ?_, hf⟩
    have hw : t.regValue .rsi = (Operand.mem (stackPtr u) : Operand 64).read u := by
      have hh := he.writes
      change t.regValue .rsi = (Operand.mem (stackPtr u + 0) : Operand 64).read u at hh
      rw [show stackPtr u + 0 = stackPtr u from BitVec.add_zero _] at hh
      exact hh
    rw [hw, hRspU]
    simpa only [outputOperand, outputSlot, Mode.outputSlotOffset, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using hOutU
  obtain ⟨t, hRunT, hInvT, hRipT, hOutT, hFrameT⟩ := hFinish
  have hFrame : AgreesExcept argumentChanges s t :=
    (hFrameU.trans hFrameT).mono (by simp [argumentChanges])
  exact ⟨t, hRunU.trans hRunT, hInvT, hRipT,
    (hFrameT.read (n := 64) (r := 4) (by decide)).trans hRspU,
    (hFrameT.read (n := 64) (r := 7) (by decide)).trans hStateU,
    hOutT, hFrame.external argumentChanges_noMem, hFrame⟩

end Sha3.Proofs.Wrapper.Finish
