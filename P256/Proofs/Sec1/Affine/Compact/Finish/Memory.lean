import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Sec1.Affine.Compressed.Finish.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem preserve {s t u : RamState} {cs : List Component} {offset len : Nat}
    (agrees : AgreesExcept cs t u)
    (memory : ∀ address count, Component.mem address count ∈ cs →
      ∃ off : BitVec 64, address = stackPtr s + off ∧
        OffsetsApart off count (-BitVec.ofNat 64 offset) len ∧ count+len < 2^64) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc covered
  cases c <;> try exact covered.elim
  case mem address count =>
    obtain ⟨off,rfl,apart,small⟩ := memory address count hc
    obtain ⟨j,hj,he⟩ := covered
    exact OffsetsApart.ne apart (stackPtr s) hj hi small (by
      simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using he.symm)

theorem load_preserve {s t : RamState} {source destination : BitVec 64}
    (bytes : ∀ i < 1, t.external[destination+BitVec.ofNat 64 i]? =
      s.external[source+BitVec.ofNat 64 i]?) :
    memLoad t.external destination 8 = memLoad s.external source 8 := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  exact bytes i hi

end P256.Proofs.Sec1.Affine.Compact.Finish
