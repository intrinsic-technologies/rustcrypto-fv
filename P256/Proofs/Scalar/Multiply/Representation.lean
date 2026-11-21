import P256.Proofs.Scalar.Multiply.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input.Memory
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Output
import P256.Proofs.Field.Schoolbook.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Adapter

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Refine
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field
open P256.Proofs.Field.Inverse.SafeGcd.Core.Input (readWords readWords_at)
open P256.Proofs.Field.Inverse.SafeGcd.Correction (limbs)
open P256.Proofs.Field.Schoolbook (packFour)

def inputs (s : RamState) : Barrett.Inputs :=
  ⟨readWords s (s.regValue .rsi), readWords s (s.regValue .rdx)⟩

theorem pack_limbs (words : Vector (BitVec 64) 4) :
    packFour (words.map BitVec.toNat) = (limbs words).toNat := by
  simp only [packFour, Vector.getElem_map, limbs, Limbs.toNat, Montgomery.wordBase]
  omega

theorem readWords_value {s : RamState} {address : BitVec 64} {value : Nat}
    (h : Nat256At s address value) :
    packFour ((readWords s address).map BitVec.toNat) = value := by
  rw [pack_limbs]
  exact readLimbs_toNat h

theorem output_nat256 {s : RamState} {address : BitVec 64} {words : Vector (BitVec 64) 4}
    (hw : WordsAt s.external address 64 words) (hr : Refine.Readable s.external address 32) :
    Nat256At s address (packFour (words.map BitVec.toNat)) := by
  rw [pack_limbs]
  exact Inverse.SafeGcd.Correction.Execution.output_nat256 hw hr

end P256.Proofs.Scalar.Multiply.Adapter
