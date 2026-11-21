import Sha3.Proofs.Wrapper.Finish.Plain.Copy224Block
import Sha3.Proofs.Wrapper.Finish.Plain.Copy256
import Sha3.Proofs.Wrapper.Finish.Plain.Copy384
import Sha3.Proofs.Wrapper.Finish.Plain.Copy512

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem copy_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {out : BitVec 64}
    {digest : Vector UInt8 v.digestBytes}
    (h : CopyPre initial v inputs split out digest s keccak mode) :
    ∃ t, Advances (returnBoundary initial) (copySteps v mode) s t ∧
      CopyPost initial v out digest s t keccak mode := by
  cases v with
  | sha224 => exact copy224_advance h
  | sha256 => exact copy256_advance h
  | sha384 => exact copy384_advance h
  | sha512 => exact copy512_advance h

end Sha3.Proofs.Wrapper.Finish.Plain
