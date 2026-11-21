import K256.Proofs.Common.Image
import K256.Proofs.Generate.Generator.Affine.Repr
import K256.Proofs.Generate.LIR.Fn10fe50.Frame
import K256.Proofs.Sec1.Serialize.Normalize.Words

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

abbrev Registers := Vector Value Reg.count
noncomputable abbrev Reaches (l : Label) (a : Registers) (m : Ram) (l' : Label) (a' : Registers) (m' : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨l', a', m'⟩, []⟩

def writes (fr : Activation) : List MemoryRegion := [fr.region, ⟨fr.rdi.toNat, 88⟩]

structure State (l : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn10fe50.frameAt l fr)
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  source : Readable m fr.rsi 120
  dest : Writable Extracted.programImage m fr.rdi 88
  srcAddr : fr.rsi = fr.rsp + 232
  dstAddr : fr.rdi = fr.rsp + 144
  high : fr.rsp.toNat + 352 ≤ 2^32
  frame : RamWriteFrame fr.original m (writes fr)

structure Coordinates (m : Ram) (base : Word) (x y z : Fin modulus) : Prop where
  repr : ∃ xl yl zl : Limbs, WordsAt m base 64 xl ∧ WordsAt m (base + 40) 64 yl ∧
    WordsAt m (base + 80) 64 zl ∧ FieldRepr xl x 8 ∧ FieldRepr yl y 8 ∧ FieldRepr zl z 8

def Normalized (fr : Activation) (m : Ram) (z : Fin modulus) : Prop :=
  ∃ a : Limbs, WordsAt m (fr.rsp - 144) 64 a ∧
    Sec1.Serialize.Normalize.Widths a ∧ limbValue a = z.val

def Inverted (fr : Activation) (m : Ram) (z : Fin modulus) : Prop :=
  ∃ a : Vector Word 4, WordsAt m (fr.rsp - 144) 64 a ∧
    (a[3].toNat * 2^64 + a[2].toNat) * 2^128 + a[1].toNat * 2^64 + a[0].toNat =
      (inverse z).val ∧ memLoad m (fr.rsp - 112) 8 = 1

structure Products (fr : Activation) (a : Registers) (m : Ram) (point : Curve.Point) : Prop where
  address : a[12] = ⟨64, fr.rsp - 144⟩
  choice : a[15] = ⟨64, (1 : Word)⟩
  pointAt : Sec1.Parser.PublicKeyAt m (fr.rsp - 144) point

end K256.Proofs.Generate.Generator.Affine
