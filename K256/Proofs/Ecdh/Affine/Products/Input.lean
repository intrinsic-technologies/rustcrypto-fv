import K256.Proofs.Ecdh.Affine.State
import K256.Proofs.Generate.Generator.Affine.Products.Input
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

structure LoadedInverse (a : Registers) (z : Fin modulus) : Prop where
  words : ∃ t : Vector Word 4, a[15] = ⟨64, t[0]⟩ ∧ a[12] = ⟨64, t[1]⟩ ∧
    a[13] = ⟨64, t[2]⟩ ∧ a[5] = ⟨64, t[3]⟩ ∧
    (z.val ≠ 0 → (t[3].toNat * 2^64 + t[2].toNat) * 2^128 + t[1].toNat * 2^64 + t[0].toNat =
      (inverse z).val)
  flag : a[0] = ⟨64, choiceBit z⟩

structure ProductCallInput (fr : Activation) (a : Registers) (m : Ram) (x y z : Fin modulus) : Prop where
  parent : CallState .l10ee37 fr (a.set 4 ⟨64, fr.rsp - 232⟩) m
  sp : a[4] = ⟨64, fr.rsp - 240⟩
  src : a[6] = ⟨64, fr.rsi⟩
  dst : a[7] = ⟨64, fr.rsp - 144⟩
  scalar : a[2] = ⟨64, fr.rsp - 232⟩
  address : a[12] = ⟨64, fr.rsp - 144⟩
  choice : a[15] = ⟨64, choiceBit z⟩
  ret : memLoad m (fr.rsp - 240) 64 = 0x10ee37
  coords : Coordinates m fr.rsi x y z
  operand : ∃ w : Limbs, WordsAt m (fr.rsp - 232) 64 w ∧ (z.val ≠ 0 → FieldRepr w (inverse z) 8)

end K256.Proofs.Ecdh.Affine
