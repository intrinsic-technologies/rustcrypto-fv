import P256.Proofs.Sec1.Decode.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem affine_prefix [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (state : AffineCallReady s t bytes)
    (effect : (callEffect (fun _ ↦ 0x1100d0) 0x10e632 t).Holds t v)
    (pre : AffineDecodePre v boundary bytes)
    (result : CalleeResult v u boundary 80 3360) :
    u.external[stackPtr s - 156]? = some (bytes.data[0]?.getD 0) := by
  have source : v.regValue .rsi = stackPtr s - 156 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.source
  have belongs : (registerRegion v .rsi 65).Contains (v.regValue .rsi).toNat := by
    change (v.regValue .rsi).toNat ≤ (v.regValue .rsi).toNat ∧
      (v.regValue .rsi).toNat < (v.regValue .rsi).toNat + 65
    omega
  have memory := result.frame (v.regValue .rsi) (by
    intro region member hin
    have cases : region = registerRegion v .rdi 80 ∨ region = Stack.region v 3360 := by
      simpa using member
    rcases cases with rfl | rfl
    · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ belongs hin
    · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ belongs hin)
  have value := pre.input.2 0 (by decide)
  change v.external[v.regValue .rsi + 0#64]? = some (bytes.data[0]?.getD 0) at value
  rw [BitVec.add_zero] at value
  rw [source] at memory value
  exact memory.trans value

end P256.Proofs.Sec1.Decode
