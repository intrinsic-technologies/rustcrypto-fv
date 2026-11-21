import ChaCha20Poly1305.Proofs.Decrypt.DetachTag
import ChaCha20Poly1305.Proofs.Decrypt.DetachBase

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash

@[refine_layout] def returnCore (v : BitVec 8) : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l1005ea
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ _ _ => [.low 0 8 v]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ _ => [.low 0 8 v]
  footprint := fun _ _ => []

theorem returnBlocks (v : BitVec 8) : ∀ l, (Layout.withFrame Fn1001f0.frameAt abiOut (returnCore v)).BlockSimulation fnCode l := by
  intro l; cases l
  x86_refine [Copy.program]

def returnFn (v : BitVec 8) := leafSpec () Fn1001f0.frameAt (returnCore v) () ()

theorem returnCorrect (v : BitVec 8) : (returnFn v).Correct :=
  provedCallee () Fn1001f0.frameAt (returnCore v) () rfl () rfl (fun _ => rfl) (returnBlocks v) (.done rfl)

theorem retAtoms {fr rs m} (v : BitVec 8) (r : Atom.All fnCode rs m (basic (physical fr) ++ [.low 0 8 v]))
    (h : Atom.All fnCode rs m (preserved fr)) :
    Atom.All fnCode rs m ((returnFn v).abi fr ++ (returnFn v).pre fr) := by
  unpack_atoms r []
  unpack_atoms h []
  join_atoms [returnFn]
  all_goals first | assumption | rfl

end ChaCha20Poly1305.Proofs.Decrypt.Detached
