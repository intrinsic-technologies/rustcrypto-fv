import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Encoding
import Base16ct.Proofs.Common.Output

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs
open Standards.RFC.BaseEncodings

theorem encoded_prefix_extend {initial s t : RamState} {input : List UInt8}
    {index : Nat} (hi : index < input.length)
    (hprefix : readOutput initial s (2 * index) = .ok (encodedBytes (input.take index)).toByteArray)
    (hframe : ∀ a : BitVec 64,
      a ≠ initial.regValue .rcx + BitVec.ofNat 64 (2 * index) →
      a ≠ initial.regValue .rcx + BitVec.ofNat 64 (2 * index) + 1 →
      t.external[a]? = s.external[a]?)
    (hhigh : t.external[initial.regValue .rcx + BitVec.ofNat 64 (2 * index)]? =
      some (Alphabet.base16Lower.character (input[index].toNat / 16)))
    (hlow : t.external[initial.regValue .rcx + BitVec.ofNat 64 (2 * index) + 1]? =
      some (Alphabet.base16Lower.character (input[index].toNat % 16)))
    (hbound : (initial.regValue .rcx).toNat + 2 * (index + 1) ≤ 2^32) :
    readOutput initial t (2 * (index + 1)) =
      .ok (encodedBytes (input.take (index + 1))).toByteArray := by
  have hprefix' : readOutput initial t (2 * index) =
      .ok (encodedBytes (input.take index)).toByteArray := by
    rw [readOutput_congr_prefix (s := s)]
    · exact hprefix
    · intro j hj
      apply hframe
      · intro he
        have := add_ofNat_inj (initial.regValue .rcx) (by omega) (by omega) he
        omega
      · intro he
        have he' : initial.regValue .rcx + BitVec.ofNat 64 j =
            initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1) := by
          simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
        have := add_ofNat_inj (initial.regValue .rcx) (by omega) (by omega) he'
        omega
  have hlow' : t.external[initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1)]? =
      some (Alphabet.base16Lower.character (input[index].toNat % 16)) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using hlow
  have hresult := readOutput_succ (readOutput_succ hprefix' hhigh) hlow'
  rw [show 2 * (index + 1) = (2 * index + 1) + 1 by omega]
  rw [List.take_succ_eq_append_getElem hi]
  simpa only [encodedBytes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using hresult

end Base16ct.Proofs.LowerEncode
