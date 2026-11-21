import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Frame
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem bytes_of_offsets {t u : RamState} {cs : List Component} {base : BitVec 64} {offset len : Nat}
    (agrees : AgreesExcept cs t u) (bound : offset+len ≤ 2^64)
    (memory : ∀ address count, Component.mem address count ∈ cs →
      ∃ off : Nat, address = base + BitVec.ofNat 64 off ∧ off+count ≤ 2^64 ∧
        (off+count ≤ offset ∨ offset+len ≤ off)) :
    ∀ i < len, u.external[base+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[base+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc covered
  cases c <;> try exact covered.elim
  case mem address count =>
    obtain ⟨off,rfl,ho,apart⟩ := memory address count hc
    obtain ⟨j,hj,eq⟩ := covered
    exact (RangeApart.offsets (base)
      (by omega) (by omega) apart) j hj i hi eq.symm

theorem montgomery_words {t u : RamState} {source destination : BitVec 64} {value : Nat}
    (input : Field.MontgomeryAt t source value)
    (readable : MemReadable t source 32) (output : MemReadable u destination 32)
    (words : ∀ j < 4, memLoad u.external (destination+BitVec.ofNat 64 (8*j)) 64 =
      memLoad t.external (source+BitVec.ofNat 64 (8*j)) 64) :
    Field.MontgomeryAt u destination value :=
  input.of_bytes_eq (HMAC.Key.Output.bytes_of_words readable output words)

end P256.Proofs.Sec1.Affine.Uncompressed.Output
