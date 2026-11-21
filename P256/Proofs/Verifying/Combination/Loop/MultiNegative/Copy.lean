import P256.Proofs.Verifying.Combination.Loop.MultiNegative.CopySetup
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.TableCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame
open P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (i : Fin 8) (rip : t.RIP = 0x10f1f0)
    (stride : t.regValue .rax = BitVec.ofNat 64 (96*i.val)) :
    ∃ fuel w, Advances boundary fuel t w ∧ DigitData s w tables digits p q u v k point left ∧
      w.RIP = 0x10f204 ∧ w.regValue .rax = BitVec.ofNat 64 (96*i.val) ∧
      ProjectiveAt w (stackPtr s - 240) (Table.oddTable (if left then p else q) i) := by
  obtain ⟨fuel,a,run,ready,_,effect⟩ := copySetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf1f0 copySetupBytes
      (by decide) (by decide +kernel)) rip
  have frameA : AgreesExcept [.reg 6, .reg 1, .reg 7, .rip] t a := effect.agrees
  have stateA := state.after_registers ready frameA (by simp [Component.Covers]) (by simp)
  have writes : a.regValue .rsi = t.regValue .rax + t.regValue .rbp ∧
      a.regValue .rcx = 12 ∧ a.regValue .rdi = stackPtr t+168 := effect.writes
  have src : a.regValue .rsi = tables+(if left then 0 else 768)+BitVec.ofNat 64 (96*i.val) := by
    rw [writes.1, stride, state.tableCursor, BitVec.add_comm]
  obtain ⟨w,runW,stateW,ripW,valueW,agreesW⟩ := Selection.table_copy pre stateA i 0xf201 240
    (by decide) (by decide) (by decide) (by decide +kernel) effect.rip src
    (writes.2.2.trans (scalar_stack_address state.rsp (offset := 168) (by decide) (by decide))) writes.2.1
  exact ⟨fuel+12,w,run.trans runW,stateW,ripW,
    (agreesW.read (n := 64) (r := 0) (by simp [copyComponents])).trans
      ((frameA.read (n := 64) (r := 0) (by simp)).trans stride), valueW⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
