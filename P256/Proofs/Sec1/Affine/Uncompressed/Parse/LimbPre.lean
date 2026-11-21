import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.LimbSelect

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem limb_call_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {out : Nat} (layout : StackCallLayout 3360 32 32 80)
    (spLayout : layout.stackOffset = 768) (inLayout : layout.inputOffset = 744)
    (outLayout : layout.outputOffset = out)
    (pre : CalleePre s boundary 0x1100d0 65 80 3360)
    (state : ScalarFrame.FrameState s t 80 3360 768)
    (rsp : stackPtr t = stackPtr s - 768) (rip : t.RIP = 0x1191c0)
    (rsi : t.regValue .rsi = 4) (rcx : t.regValue .rcx = 4)
    (source : t.regValue .rdx = stackPtr s - 744)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 out)
    (ret : InProgram (returnBoundary t).rip) : LimbSelect.Pre t boundary := by
  have base : CalleePre t boundary 0x1191c0 32 32 80 .rdx :=
    CalleePre.of_stack pre layout state.bindingsSupported state.machine state.directionFlag
      state.loaded state.allocated rip (spLayout ▸ rsp) (inLayout ▸ source) (outLayout ▸ output) ret
  have empty (a : Nat) : ¬ (registerRegion t .rsi 0).Contains a := by
    change ¬ ((t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 0)
    omega
  refine {
    toCalleePre := { base with
      inputBounded := ?_
      inputAllocated := fun a ha => (empty a.toNat ha).elim
      separation := ?_ }
    leftCount := rsi
    rightCount := rcx
    sourceBounded := base.inputBounded
    sourceAllocated := base.inputAllocated
    sourceOutput := base.separation 0 1 (by decide)
    sourceStack := base.separation 0 2 (by decide) }
  · change (t.regValue .rsi).toNat + 0 < 2^32
    rw [rsi]
    decide
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · exact fun a ha _ => empty a ha
    · exact fun a ha _ => empty a ha
    · exact base.separation 1 2 (by decide)

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
