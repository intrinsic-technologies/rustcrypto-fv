import P256.Proofs.Verifying.Message.Convert.Ready

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program.Routines Program Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {key : Curve.Point} {r scalarS : Nat}
    (pre : Pre initial boundary message) (input : InputAt initial key r scalarS)
    (nonidentity : key ≠ .infinity) (state : Hash.Result initial s boundary message) :
    ∃ t, Call.Prepared initial t boundary message key := by
  cases key with
  | infinity => exact (nonidentity rfl).elim
  | affine x y =>
    obtain ⟨h, headState⟩ := head pre state
    obtain ⟨cy, yState⟩ := copy_y pre input headState
    obtain ⟨cx, xState⟩ := copy_x pre input yState
    obtain ⟨cz, zState⟩ := copy_z pre xState
    obtain ⟨identity, identityState⟩ := copy_identity pre zState
    obtain ⟨choice, choiceState⟩ := choose pre input identityState
    obtain ⟨sx, selectedX⟩ := select_x pre choiceState
    obtain ⟨sy, selectedY⟩ := select_y pre selectedX
    obtain ⟨sz, selectedZ⟩ := select_z pre selectedY
    exact prepare_core pre selectedZ

end P256.Proofs.Verifying.Message.Convert
