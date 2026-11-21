import P256.Proofs.Sec1.SquareRoot.Interface
import P256.Proofs.Program.Code
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem parameters_loaded {s : RamState} (h : ProgramLoaded s) :
    ParametersAt s 0x202f28 := by
  have hbytes : ∀ i : Fin 112,
      Extracted.programSections.fetchByte (0x202f28 + BitVec.ofNat 64 i.val) =
        some (parameterBytes[i.val]!) := by decide +kernel
  intro i hi
  exact h _ _ (hbytes ⟨i, hi⟩)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem exponent_loaded {s : RamState} (h : ProgramLoaded s) :
    Nat256At s 0x202fb8 ((P256.Spec.Operations.domain.p + 1) / 4) := by
  refine ⟨by decide +kernel, ?_⟩
  have hbytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202fb8 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (((P256.Spec.Operations.domain.p + 1) / 4) / 256 ^ i.val % 256)) :=
    by decide +kernel
  intro i hi
  exact h _ _ (hbytes ⟨i, hi⟩)

set_option maxRecDepth 4096 in
theorem parameters_modulus {s : RamState} {address : BitVec 64}
    (h : ParametersAt s address) : Nat256At s address P256.Spec.Operations.domain.p := by
  refine ⟨by decide +kernel, ?_⟩
  have hbytes : ∀ i : Fin 32, parameterBytes[i.val]! =
      UInt8.ofNat (P256.Spec.Operations.domain.p / 256 ^ i.val % 256) := by decide +kernel
  intro i hi
  rw [h i (by omega), hbytes ⟨i, hi⟩]

set_option maxRecDepth 4096 in
theorem parameters_one {s : RamState} {address : BitVec 64}
    (h : ParametersAt s address) : MontgomeryAt s (address + 32) 1 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have hbytes : ∀ i : Fin 32, parameterBytes[32 + i.val]! =
      UInt8.ofNat ((1 * 2^256 % P256.Spec.Operations.domain.p) / 256 ^ i.val % 256) :=
    by decide +kernel
  intro i hi
  have he : address + 32 + BitVec.ofNat 64 i = address + BitVec.ofNat 64 (32 + i) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  rw [he, h (32+i) (by omega), hbytes ⟨i, hi⟩]

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 512 in
theorem parameters_radixSquared {s : RamState} {address : BitVec 64}
    (h : ParametersAt s address) :
    Nat256At s (address + 64) (2^512 % P256.Spec.Operations.domain.p) := by
  refine ⟨by decide +kernel, ?_⟩
  have hbytes : ∀ i : Fin 32, parameterBytes[64 + i.val]! =
      UInt8.ofNat ((2^512 % P256.Spec.Operations.domain.p) / 256 ^ i.val % 256) :=
    by decide +kernel
  intro i hi
  have he : address + 64 + BitVec.ofNat 64 i = address + BitVec.ofNat 64 (64 + i) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  rw [he, h (64+i) (by omega), hbytes ⟨i, hi⟩]

theorem parameters_inverse_bytes {s : RamState} {address : BitVec 64}
    (h : ParametersAt s address) :
    X86Proofs.Bytes s.external (address + 96) 8 (X86Proofs.storedByte (-1 : BitVec 64)) := by
  have hb := X86Proofs.Bytes.sub h 96 8 (by decide)
  apply X86Proofs.Bytes.congr hb
  have he : ∀ i : Fin 8, parameterBytes[96 + i.val]! =
      X86Proofs.storedByte (-1 : BitVec 64) i.val := by decide +kernel
  exact fun i hi => he ⟨i, hi⟩

theorem parameters_inverse {s : RamState} {address : BitVec 64}
    (h : ParametersAt s address) :
    loadBytes s.external (address + 96) 8 = .ok (-1 : BitVec 64) :=
  (parameters_inverse_bytes h).loadBytes64

end P256.Proofs.Sec1.SquareRoot
