import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Words
import K256.Proofs.Sec1.Affine.Uncompressed.Squares

namespace K256.Proofs.Sec1.Affine.Compressed

open K256.Proofs.Common.Field

private def squareSecondState (s : Vector Word 8) : Vector Word 7 :=
  #v[s[0], s[1], s[3], s[2], s[5], s[6], (BitVec.setWidth 32 s[4]).setWidth 64 &&& 0xf]

private def squareThirdState (s : Vector Word 7) : Vector Word 7 :=
  #v[s[0], s[1], s[3], s[2], s[4], s[5], s[6]]

private theorem inputSquare_second (a : Limbs) (s : Vector Word 8) :
    inputSquare120705 a s = squareSecondState (Uncompressed.squareX11FC4F a s) := rfl

private theorem inputSquare_third (a : Limbs) (s : Vector Word 8) :
    let u := Uncompressed.squareX11FC4F a s
    inputSquare120777H a (squareSecondState u) =
      squareThirdState (Uncompressed.squareX11FCAB a u) := rfl

private theorem inputSquare_fourth (a : Limbs) (s : Vector Word 7) :
    inputSquare1207E5H a (squareThirdState s) = Uncompressed.squareX11FD1DH a s := rfl

private theorem inputSquare_fifth (a : Limbs) (s : Vector Word 9) :
    inputSquare120856 a s = Uncompressed.squareX11FD89 a s := rfl

private theorem inputSquare_finish (s : Vector Word 7) :
    inputSquare1208C0 s = Uncompressed.squareX11FDF2 s := by
  have mask : (0xffffffffffffe &&& s[0] : Word) = s[0] &&& 0xffffffffffffe :=
    BitVec.and_comm _ _
  have same : inputSquareFinish s (s[0] &&& 0xffffffffffffe) =
      Uncompressed.squareX11FDF2 s := rfl
  exact (congrArg (inputSquareFinish s) mask).trans same

private theorem inputSquare_eq_squareX (a : Limbs) : inputSquare a = Uncompressed.squareX a := by
  unfold inputSquare Uncompressed.squareX
  extract_lets c1 c2 c3 c4 c5 u1 u2 u3 u4 u5
  have e1 : c1 = u1 := rfl
  have e2 : c2 = squareSecondState u2 :=
    (congrArg (inputSquare120705 a) e1).trans (inputSquare_second a u1)
  have e3 : c3 = squareThirdState u3 :=
    (congrArg (inputSquare120777H a) e2).trans (inputSquare_third a u1)
  have e4 : c4 = u4 :=
    (congrArg (inputSquare1207E5H a) e3).trans (inputSquare_fourth a u3)
  have e5 : c5 = u5 :=
    (congrArg (inputSquare120856 a) e4).trans (inputSquare_fifth a u4)
  exact (congrArg inputSquare1208C0 e5).trans (inputSquare_finish u5)

theorem inputSquare_repr (a : Limbs) (x : Fin modulus) (h : FieldRepr a x 8) :
    FieldRepr (inputSquare a) (x * x) 1 := by
  rw [inputSquare_eq_squareX]
  exact Uncompressed.squareX_repr a x h

end K256.Proofs.Sec1.Affine.Compressed
