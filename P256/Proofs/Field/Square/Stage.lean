import P256.Proofs.Field.Square.Entry
import P256.Proofs.Field.Montgomery.Wrapper.Schoolbook

set_option autoImplicit false

namespace P256.Proofs.Field.Square

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Montgomery.Wrapper

theorem schoolbook_stage [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : CalleePre s boundary 0x113800 32 32 280)
    (ha : Nat256At s (s.regValue .rsi) a) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t ∧ t.RIP = 0x113823 ∧
      Bytes t.external (scratch s + 64) 64 (fun i => UInt8.ofNat ((a*a) / 256^i % 256)) := by
  obtain ⟨entered, entry⟩ := Square.schoolbook_entry_correct pre
  have state := entered_state pre entry
  have left : Nat256At entered (entered.regValue .rsi) a := by
    rw [entry.left]
    exact input_of_frame pre state.frame ha
  have right : Nat256At entered (entered.regValue .rcx) a := by
    rw [entry.right]
    exact input_of_frame pre state.frame ha
  exact schoolbook_of_entry pre entry left right

end P256.Proofs.Field.Square
