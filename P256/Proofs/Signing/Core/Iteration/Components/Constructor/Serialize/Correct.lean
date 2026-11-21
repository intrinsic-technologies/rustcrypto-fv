import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize.Body
import P256.Proofs.Program.LeafReturn

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem scalar_encode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {d reserve : Nat} (pre : CalleePre s boundary 0x115960 32 32 reserve)
    (scalar : Nat256At s (s.regValue .rsi) d) :
    ∃ t, CalleeResult s t boundary 32 reserve ∧
      Bytes t.external (s.regValue .rdi) 32
        (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) ∧
      t.regValue .rax = s.regValue .rdi ∧
      AgreesExcept (leafComponents (s.regValue .rdi) 32 [0,1,2,6,7] ++ [.reg 4,.rip]) s t := by
  obtain ⟨fuel, stored, run, ready, rip, ag, bytes, rax⟩ := body_correct pre scalar
  have narrow : AgreesExcept (leafComponents (s.regValue .rdi) 32 [0,1,2,6,7]) s stored :=
    ag.mono (by simp [components, leafComponents])
  obtain ⟨t, result, memory, retax, frame⟩ := leaf_return [0,1,2,6,7]
    (by decide) (by decide) pre run ready rip (codeOffset := 0x1598d)
    (by decide) (by decide +kernel) narrow
  refine ⟨t, result, ?_, retax.trans rax, frame⟩
  intro i hi
  rw [memory]
  exact bytes i hi

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize
