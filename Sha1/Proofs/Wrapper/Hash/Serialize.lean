import Sha1.Spec.Hasher

set_option autoImplicit false

namespace Sha1.Proofs.Wrapper.Hash.Serialize

open Sha1.Spec


def stateBytes (H : Vector (BitVec 32) 5) : ByteArray :=
  ⟨(Hasher.stateBytes H).toArray⟩

theorem stateBytes_size (H : Vector (BitVec 32) 5) :
    (stateBytes H).size = 20 := by
  change (Hasher.stateBytes H).toArray.size = 20
  rw [Vector.size_toArray]


end Sha1.Proofs.Wrapper.Hash.Serialize
