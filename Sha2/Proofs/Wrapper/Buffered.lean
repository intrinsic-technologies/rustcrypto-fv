import Sha2.Proofs.Wrapper.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

variable {v : Variant}

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem buffered_of_bytes [Bindings] {initial s t : RamState} {message : ByteArray}
    (input : Buffered initial s message v) (preserved : Preserved initial t v)
    (bytes : ∀ a : BitVec 64, t.external[a]? = s.external[a]?) : Buffered initial t message v := by
  refine ⟨preserved, hashState_of_bytes input.hashWords (fun i _ => bytes _),
    ⟨input.tailBytes.1, fun i => (bytes _).trans (input.tailBytes.2 i)⟩,
    (bytes _).trans input.tailLength, ?_⟩
  rw [← input.blocks]
  apply memLoad_congr
  intro i _
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [bytes]

theorem buffered_of_agrees [Bindings] {initial s t : RamState} {inputs : Array Input}
    {message : ByteArray} {fuel : Nat} {components : List Component}
    (ctx : Context initial inputs v) (input : Buffered initial s message v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components := by simp) :
    Buffered initial t message v :=
  buffered_of_bytes input
    (preserved_of_agrees ctx input.toPreserved run ready frame
      (fun c hc a ha => (noMem c hc a ha).elim) kept4 hdf)
    (fun a => frame.memory a (fun c hc => noMem c hc a))

end Sha2.Proofs.Wrapper
