import P256.Proofs.Verifying.Combination.Loop.MultiNegative.NegateSetup
import P256.Proofs.Field.Preserve
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_negate [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (rip : t.RIP = 0x10f22c) :
    ∃ fuel w, Advances boundary fuel t w ∧ DigitData s w tables digits p q u v k point left ∧
      w.RIP = 0x10f23c ∧ w.regValue .rdi = stackPtr s-112 ∧
      w.regValue .rsi = stackPtr s-368 ∧ w.regValue .r14 = stackPtr s-112 ∧
      w.external = t.external := by
  obtain ⟨fuel,w,run,ready,_,effect⟩ := negateSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf22c negateSetupBytes
      (by decide) (by decide +kernel)) rip
  have frame : AgreesExcept [.reg 14, .reg 7, .reg 6, .rip] t w := effect.agrees
  have writes : w.regValue .r14 = stackPtr t+296 ∧ w.regValue .rdi = stackPtr t+296 ∧
      w.regValue .rsi = stackPtr t+40 := effect.writes
  have dest := scalar_stack_address state.rsp (offset := 296) (by decide) (by decide)
  have src := scalar_stack_address state.rsp (offset := 40) (by decide) (by decide)
  exact ⟨fuel,w,run,state.after_registers ready frame (by simp [Component.Covers]) (by simp),
    effect.rip,writes.2.1.trans dest,writes.2.2.trans src,writes.1.trans dest,
    frame.external (by simp [Component.Covers])⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
