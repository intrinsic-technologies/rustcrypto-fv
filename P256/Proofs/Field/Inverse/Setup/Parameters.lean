import P256.Proofs.Program.RipCopy
import P256.Proofs.Program.Code
import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem parameters_modulus {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x202f28 P256.Spec.Operations.domain.p := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202f28 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (P256.Spec.Operations.domain.p / 256 ^ i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

set_option exponentiation.threshold 512 in
theorem parameters_radixSquared {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x202f68 (2^512 % P256.Spec.Operations.domain.p) := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202f68 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat ((2^512 % P256.Spec.Operations.domain.p) / 256 ^ i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

abbrev parameterWords : Vector (Nat × BitVec 32 × BitVec 8) 8 :=
  #v[(0x1409c, 0xeee9d, 64), (0x140a8, 0xeee89, 56),
     (0x140b4, 0xeee75, 48), (0x140c0, 0xeee61, 40),
     (0x140da, 0xeee87, 72), (0x140e6, 0xeee83, 80),
     (0x140f2, 0xeee7f, 88), (0x140fe, 0xeee7b, 96)]

theorem parameter_word_code {s : RamState} (loaded : ProgramLoaded s) (i : Fin 8) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
      (RipCopy.bytes parameterWords[i].2.1 parameterWords[i].2.2)) s := by
  have bound : ∀ i : Fin 8, parameterWords[i].1 +
      (RipCopy.bytes parameterWords[i].2.1 parameterWords[i].2.2).length ≤ 118431 := by
    decide +kernel
  have code : ∀ i : Fin 8, Extracted.textBytes.toListFrom parameterWords[i].1
      (RipCopy.bytes parameterWords[i].2.1 parameterWords[i].2.2).length =
        RipCopy.bytes parameterWords[i].2.1 parameterWords[i].2.2 := by
    decide +kernel
  exact programText_slice (programLoaded_codeIn loaded) _ _ (bound i) (code i)

theorem parameter_word_copy [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (i : Fin 8) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip)
    (pre : RipCopy.Pre (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
      parameterWords[i].2.1 parameterWords[i].2.2 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
        (RipCopy.bytes parameterWords[i].2.1 parameterWords[i].2.2)) t ∧
      (RipCopy.effect (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
        parameterWords[i].2.1 parameterWords[i].2.2 s).Holds s t := by
  have bounds : ∀ i : Fin 8, parameterWords[i].1 + 12 < 118431 := by decide +kernel
  have next (offset : Nat) (bound : offset ≤ 12) :
      (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1) +
        BitVec.ofNat 64 offset ≠ boundary.rip := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact boundary_ne_program outside (inProgram_of_textOffset _ (by have := bounds i; omega))
  exact RipCopy.copy_word boundary _ _ _ (next 7 (by decide)) (next 12 (by decide))
    s ready (parameter_word_code loaded i) pre

end P256.Proofs.Field.Inverse
